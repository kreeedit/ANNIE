# -*- coding: utf-8 -*-
import tkinter as tk
from tkinter import messagebox
from tkinter import ttk
import json
import uuid
import re
import threading
from bisect import bisect_left, bisect_right
import requests

class LLMMixin:
    """Generative LLM few-shot agent."""

    def run_llm_agent_from_hotkey(self, event=None):
        """Called when the 'g' key is pressed."""
        if getattr(self, '_is_annotating_ai', False): return
        if not self.current_file_path: return

        # Check if we have an API key for the currently selected provider
        key_exists = False
        if self.llm_provider == "Anthropic (Claude)" and self.claude_api_key.strip(): key_exists = True
        elif self.llm_provider == "OpenAI" and self.openai_api_key.strip(): key_exists = True
        elif self.llm_provider == "Together AI" and self.together_api_key.strip(): key_exists = True
        elif self.llm_provider == "Hugging Face" and self.hf_api_key.strip(): key_exists = True

        # If all data is available, start LLM immediately; otherwise open settings dialog
        if key_exists and self.llm_model:
            self._start_llm_agent()
        else:
            self.show_llm_settings_dialog()

    def show_llm_settings_dialog(self):
        if not self.current_file_path:
            messagebox.showwarning("No File", "Please load a chart first!", parent=self.root)
            return

        dialog = tk.Toplevel(self.root)
        dialog.title("Generative LLM Agent Settings")
        dialog.geometry("500x520")
        dialog.transient(self.root)
        dialog.grab_set()

        main_frame = tk.Frame(dialog, padx=20, pady=15)
        main_frame.pack(fill=tk.BOTH, expand=True)

        tk.Label(main_frame, text="1. Select Provider API:", font=('TkDefaultFont', 10, 'bold')).pack(anchor=tk.W, pady=(0, 5))
        provider_var = tk.StringVar(value=self.llm_provider)
        provider_combo = ttk.Combobox(main_frame, textvariable=provider_var,
                                      values=["OpenAI", "Anthropic (Claude)", "Together AI", "Hugging Face"],
                                      state="readonly")
        provider_combo.pack(fill=tk.X, pady=(0, 15))

        tk.Label(main_frame, text="2. Model ID:", font=('TkDefaultFont', 10, 'bold')).pack(anchor=tk.W, pady=(0, 5))
        model_var = tk.StringVar(value=self.llm_model)
        api_key_var = tk.StringVar()

        if self.llm_provider == "Anthropic (Claude)": api_key_var.set(self.claude_api_key)
        elif self.llm_provider == "OpenAI": api_key_var.set(self.openai_api_key)
        elif self.llm_provider == "Together AI": api_key_var.set(self.together_api_key)
        else: api_key_var.set(self.hf_api_key)

        def on_provider_change(*args):
            p = provider_var.get()
            model_var.set(self.llm_models.get(p, ""))

            if p == "Anthropic (Claude)": api_key_var.set(self.claude_api_key)
            elif p == "OpenAI": api_key_var.set(self.openai_api_key)
            elif p == "Together AI": api_key_var.set(self.together_api_key)
            else: api_key_var.set(self.hf_api_key)

        provider_var.trace_add("write", on_provider_change)

        model_entry = tk.Entry(main_frame, textvariable=model_var)
        model_entry.pack(fill=tk.X, pady=(0, 5))

        help_text = ("OpenAI: gpt-4o-mini\n"
                     "Claude: claude-sonnet-4-6\n"
                     "Together: meta-llama/Llama-3.3-70B-Instruct-Turbo\n"
                     "HF: HuggingFaceH4/zephyr-7b-beta")
        tk.Label(main_frame, text=help_text, fg="grey", justify=tk.LEFT).pack(anchor=tk.W, pady=(0, 15))

        tk.Label(main_frame, text="3. API Key:", font=('TkDefaultFont', 10, 'bold')).pack(anchor=tk.W, pady=(0, 5))
        api_entry = tk.Entry(main_frame, textvariable=api_key_var, show="*")
        api_entry.pack(fill=tk.X, pady=(0, 15))

        tk.Label(main_frame, text="4. Few-Shot Examples (from Session Memory):", font=('TkDefaultFont', 10, 'bold')).pack(anchor=tk.W, pady=(0, 5))
        examples_var = tk.IntVar(value=self.llm_few_shot_count)
        examples_spin = tk.Spinbox(main_frame, from_=0, to=10, textvariable=examples_var)
        examples_spin.pack(fill=tk.X, pady=(0, 15))

        def on_run():
            self.llm_provider = provider_var.get()
            self.llm_model = model_var.get().strip()
            self.llm_models[self.llm_provider] = self.llm_model
            self.llm_few_shot_count = examples_var.get()

            entered_key = api_key_var.get().strip()
            if self.llm_provider == "Anthropic (Claude)": self.claude_api_key = entered_key
            elif self.llm_provider == "OpenAI": self.openai_api_key = entered_key
            elif self.llm_provider == "Together AI": self.together_api_key = entered_key
            else: self.hf_api_key = entered_key

            if not entered_key:
                messagebox.showerror("Error", "Please provide an API Key for the selected provider.", parent=dialog)
                return

            self._save_api_keys()

            dialog.destroy()
            self._start_llm_agent()

        btn_frame = tk.Frame(main_frame)
        btn_frame.pack(fill=tk.X, pady=(20, 0), side=tk.BOTTOM)
        tk.Button(btn_frame, text="Run LLM Agent", command=on_run, bg="plum").pack(side=tk.RIGHT, padx=5)
        tk.Button(btn_frame, text="Cancel", command=dialog.destroy).pack(side=tk.RIGHT)
        dialog.wait_window()

    def _build_few_shot_prompt(self, current_text):
        active_tags = self.get_active_tags()
        prompt = (f"You are an expert medieval archivist performing Named Entity Recognition (NER). "
                  f"Extract entities strictly belonging to these tags: {', '.join(active_tags)}.\n"
                  f"Return ONLY a valid JSON array of objects with 'text' and 'tag' keys. Do not write markdown, explanations, or introductory text. Just the JSON array starting with [ and ending with ].\n\n")

        if self.llm_few_shot_count > 0:
            similar_examples = self._retrieve_similar_examples(current_text, top_k=self.llm_few_shot_count)

            for i, (ex_text, entities) in enumerate(similar_examples):
                # Request only entities currently active in UI
                json_entities = [{"text": e["text"], "tag": e["tag"]} for e in entities if e["tag"] in active_tags]
                if not json_entities: continue

                prompt += f"### Example {i + 1}\nInput:\n{ex_text}\nOutput:\n{json.dumps(json_entities, ensure_ascii=False)}\n\n"

        prompt += f"### Target Task\nInput:\n{current_text}\nOutput:\n"
        return prompt

    def _start_llm_agent(self):
        if getattr(self, '_is_annotating_ai', False): return
        self._is_annotating_ai = True
        self.status_var.set(f"Generative LLM ({self.llm_provider}) call in progress...")
        self.progress_bar.start()

        full_text = self.text_area.get("1.0", tk.END).strip()

        def thread_target():
            try:
                print(f"\n[{self.llm_provider}] Building prompt from memory...")
                prompt = self._build_few_shot_prompt(full_text)
                self._update_status_threadsafe("Waiting for LLM response...")

                result_json_str = ""

                if self.llm_provider == "OpenAI":
                    print(f"[OpenAI] Call: {self.llm_model} ...")
                    headers = {"Authorization": f"Bearer {self.openai_api_key}", "Content-Type": "application/json"}
                    payload = {"model": self.llm_model, "messages": [{"role": "user", "content": prompt}], "max_tokens": 4096, "temperature": 0.1}
                    response = requests.post("https://api.openai.com/v1/chat/completions", headers=headers, json=payload, timeout=(15, 300))
                    response.raise_for_status()
                    res_data = response.json()
                    result_json_str = res_data["choices"][0]["message"]["content"]

                elif self.llm_provider == "Together AI":
                    print(f"[Together AI] Call: {self.llm_model} ...")
                    headers = {"Authorization": f"Bearer {self.together_api_key}", "Content-Type": "application/json"}
                    payload = {"model": self.llm_model, "messages": [{"role": "user", "content": prompt}], "max_tokens": 4096, "temperature": 0.1}
                    response = requests.post("https://api.together.xyz/v1/chat/completions", headers=headers, json=payload, timeout=(15, 300))
                    response.raise_for_status()
                    res_data = response.json()
                    result_json_str = res_data["choices"][0]["message"]["content"]

                # --- HUGGING FACE API ---
                elif self.llm_provider == "Hugging Face":
                    print(f"[Hugging Face] call: {self.llm_model} ...")

                    api_url = "https://router.huggingface.co/v1/chat/completions"

                    headers = {"Authorization": f"Bearer {self.hf_api_key}", "Content-Type": "application/json"}
                    payload = {
                        "model": self.llm_model,
                        "messages": [{"role": "user", "content": prompt}],
                        "max_tokens": 4096,
                        "temperature": 0.1
                    }

                    response = requests.post(api_url, headers=headers, json=payload, timeout=(15, 300))

                    response.raise_for_status()
                    res_data = response.json()
                    result_json_str = res_data["choices"][0]["message"]["content"]

                elif self.llm_provider == "Anthropic (Claude)":
                    print(f"[Anthropic] call: {self.llm_model} ...")
                    headers = {"x-api-key": self.claude_api_key, "anthropic-version": "2023-06-01", "content-type": "application/json"}
                    payload = {"model": self.llm_model, "max_tokens": 4096, "temperature": 0.1, "messages": [{"role": "user", "content": prompt}]}
                    response = requests.post("https://api.anthropic.com/v1/messages", headers=headers, json=payload, timeout=(15, 300))
                    response.raise_for_status()
                    res_data = response.json()
                    result_json_str = res_data["content"][0]["text"]

                print(f"[LLM Agent] Successful API response received! Processing...\n")

                start_idx = result_json_str.find('[')
                if start_idx == -1:
                    raise ValueError(f"The LLM did not generate a JSON list. Raw response: {result_json_str}")

                json_str = result_json_str[start_idx:]

                extracted_entities = []
                try:
                    extracted_entities = json.loads(json_str)
                except json.JSONDecodeError:
                    print("[LLM Agent] Attention: Truncated JSON! I'm trying to fix it...")
                    last_brace_idx = json_str.rfind('}')
                    if last_brace_idx != -1:
                        fixed_json_str = json_str[:last_brace_idx+1] + ']'
                        try:
                            extracted_entities = json.loads(fixed_json_str)
                            print("[LLM Agent] Truncated JSON successfully repaired!")
                        except json.JSONDecodeError as e2:
                            raise ValueError(f"Unable to repair incomplete JSON: {e2}")
                    else:
                        raise ValueError("Unintelligible JSON format.")

                llm_annotations = [e for e in extracted_entities if isinstance(e, dict) and "text" in e and "tag" in e]

                self._update_status_threadsafe(f"DONE|LLM replied: {len(llm_annotations)} entity. Matching to text...")

                text_to_tag_map = {item['text'].strip(): item['tag'] for item in llm_annotations if item.get('text', '').strip()}
                memory_anns = self._get_memory_predictions(full_text)

                line_starts = [0]
                for i, char in enumerate(full_text):
                    if char == '\n': line_starts.append(i + 1)
                line_starts.append(len(full_text) + 1)

                def offset_to_tkinter(offset):
                    line_idx = bisect_right(line_starts, offset) - 1
                    line = line_idx + 1
                    char = offset - line_starts[line_idx]
                    return f"{line}.{char}"

                ai_anns = []
                compiled_regexes = []
                for text, tag in text_to_tag_map.items():
                    pattern = r'\b' + re.escape(text) + r'\b'
                    compiled_regexes.append((re.compile(pattern, re.IGNORECASE), tag, text))
                compiled_regexes.sort(key=lambda x: len(x[2]), reverse=True)

                for regex, tag, _ in compiled_regexes:
                    for match in regex.finditer(full_text):
                        matched_text = match.group()
                        start_pos = offset_to_tkinter(match.span()[0])
                        end_pos = offset_to_tkinter(match.span()[1])
                        start_l, start_c = map(int, start_pos.split('.'))
                        end_l, end_c = map(int, end_pos.split('.'))

                        ai_anns.append({
                            'id': uuid.uuid4().hex, 'start_line': start_l, 'start_char': start_c,
                            'end_line': end_l, 'end_char': end_c, 'text': matched_text,
                            'tag': tag, 'propagated': True, 'score': 1.0
                        })

                self.root.after(0, self._apply_ensemble_to_ui, memory_anns, ai_anns)

            except requests.exceptions.HTTPError as e:
                error_msg = f"API Error: {e.response.status_code}"
                try:
                    err_json = e.response.json()
                    error_msg = err_json.get('error', err_json)
                except: pass
                self._update_status_threadsafe(f"DONE|{error_msg}")
                print(f"\n[SERIOUS API ERROR]:\n{e.response.text}\n")
            except Exception as e:
                self._update_status_threadsafe(f"DONE|Error: {e}")
                print(f"\n[ERROR DETAILS] {e}\n")
            finally:
                self.root.after(0, lambda: setattr(self, '_is_annotating_ai', False))

        threading.Thread(target=thread_target, daemon=True).start()
