# -*- coding: utf-8 -*-
import tkinter as tk
from tkinter import messagebox
from tkinter import ttk
import uuid
import re
import traceback
import threading
import torch
import queue
from bisect import bisect_left, bisect_right

class AIMixin:
    """Ensemble (session-memory + HF) AI annotation."""

    def predict_from_session_memory(self):
        """Manual button: Predicts using ONLY Session Memory (Knowledge Base)."""
        if not self.current_file_path:
            messagebox.showwarning("No File", "Please load a chart first!", parent=self.root)
            return

        self.status_var.set("Analyzing Session Memory...")
        self.progress_bar.start()
        self.root.update()

        try:
            with open(self.current_file_path, 'r', encoding='utf-8') as f: content = f.read()
        except Exception as e:
            self.progress_bar.stop()
            messagebox.showerror("Error", f"Failed to read file:\n{e}", parent=self.root)
            return

        memory_anns = self._get_memory_predictions(content)
        self._apply_ensemble_to_ui(memory_anns, [])

    def _get_memory_predictions(self, content):
        """Builds Knowledge Base from other files and predicts tags for current text."""
        knowledge_base = {}
        for f_path, data in self.annotations.items():
            if f_path == self.current_file_path: continue
            for ann in data.get("entities", []):
                txt = ann.get('text', '').strip()
                if not txt or len(txt) < 2: continue
                tag = ann['tag']
                txt_lower = txt.lower()
                if txt_lower not in knowledge_base: knowledge_base[txt_lower] = {}
                knowledge_base[txt_lower][tag] = knowledge_base[txt_lower].get(tag, 0) + 1

        final_mapping = {}
        for txt_lower, tag_counts in knowledge_base.items():
            best_tag = max(tag_counts.items(), key=lambda x: x[1])[0]
            if self.tag_active_states.get(best_tag, True): final_mapping[txt_lower] = best_tag

        memory_annotations = []
        if not final_mapping: return memory_annotations

        line_starts = [0]
        for i, char in enumerate(content):
            if char == '\n': line_starts.append(i + 1)
        line_starts.append(len(content) + 1)

        sorted_texts = sorted(final_mapping.keys(), key=len, reverse=True)
        chunk_size = 1500

        for i in range(0, len(sorted_texts), chunk_size):
            chunk = sorted_texts[i:i+chunk_size]
            pattern = '|'.join(r'\b' + re.escape(text) + r'\b' for text in chunk)
            regex = re.compile(pattern, re.IGNORECASE)

            for match in regex.finditer(content):
                matched_text = match.group()
                tag = final_mapping.get(matched_text.lower())
                if not tag: continue

                start_index, end_index = match.span()
                start_pos = self._char_offset_to_tkinter_index_from_offsets(line_starts, start_index)
                end_pos = self._char_offset_to_tkinter_index_from_offsets(line_starts, end_index)
                start_l, start_c = map(int, start_pos.split('.'))
                end_l, end_c = map(int, end_pos.split('.'))

                memory_annotations.append({
                    'id': uuid.uuid4().hex, 'start_line': start_l, 'start_char': start_c,
                    'end_line': end_l, 'end_char': end_c, 'text': matched_text,
                    'tag': tag, 'propagated': True, 'source': 'memory'
                })
        return memory_annotations

    def _apply_ensemble_to_ui(self, memory_anns, ai_anns):
        """Combines Memory and AI predictions, giving priority to Memory."""
        try:
            entities_list = self.annotations.setdefault(self.current_file_path, {}).setdefault("entities", [])
            added_memory_count, added_ai_count = 0, 0
            allow_overlap = self.allow_multilabel_overlap.get()

            for ann in memory_anns:
                is_dup = any(e['start_line'] == ann['start_line'] and e['start_char'] == ann['start_char'] and e['end_line'] == ann['end_line'] and e['end_char'] == ann['end_char'] and e['tag'] == ann['tag'] for e in entities_list)
                if not is_dup and (allow_overlap or not self._is_overlapping_in_list(ann['start_line'], ann['start_char'], ann['end_line'], ann['end_char'], entities_list)):
                    entities_list.append(ann)
                    self._add_to_entity_lookup_map(ann)
                    added_memory_count += 1

            for ann in ai_anns:
                if not self._is_overlapping_in_list(ann['start_line'], ann['start_char'], ann['end_line'], ann['end_char'], entities_list):
                    entities_list.append(ann)
                    self._add_to_entity_lookup_map(ann)
                    added_ai_count += 1

            entities_list.sort(key=lambda a: (a['start_line'], a['start_char']))
            self.apply_annotations_to_text()
            self.update_entities_list()
            self._update_button_states()

            # Pass the final success message through the queue to ensure UI update
            self._update_status_threadsafe(f"DONE|Ensemble Complete. Added: {added_memory_count} (Memory) + {added_ai_count} (AI).")
        except Exception as e:
            traceback.print_exc()
            self._update_status_threadsafe(f"DONE|Error applying annotations to UI: {e}")
        finally:
            # Ensure AI lock is lifted
            self._is_annotating_ai = False

    def run_ai_annotation_from_hotkey(self, event=None):
        if self._is_annotating_ai: return
        if not self.current_file_path: return
        if not self.current_ai_models: self._show_ai_settings_dialog()
        else: self._start_ai_annotation_process(self.current_ai_models)

    def pre_annotate_with_ai(self):
        if self._is_annotating_ai: return
        if not self.current_file_path:
            messagebox.showwarning("No File", "Please load a file first.", parent=self.root)
            return
        self._show_ai_settings_dialog()

    def _show_ai_settings_dialog(self):
        dialog = tk.Toplevel(self.root)
        dialog.title("Hybrid AI Pre-annotation Settings")
        dialog.geometry("550x650")
        dialog.transient(self.root)
        dialog.grab_set()

        main_frame = tk.Frame(dialog, padx=10, pady=10)
        main_frame.pack(fill=tk.BOTH, expand=True)

        tk.Label(main_frame, text="1. Selected Models (max 2):", font=('TkDefaultFont', 10, 'bold')).pack(anchor=tk.W, pady=(0, 5))
        selected_models_frame = tk.Frame(main_frame)
        selected_models_frame.pack(fill=tk.X)
        self.selected_models_listbox = tk.Listbox(selected_models_frame, height=2, exportselection=False)
        self.selected_models_listbox.pack(side=tk.LEFT, fill=tk.X, expand=True)
        selected_models_scrollbar = tk.Scrollbar(selected_models_frame, command=self.selected_models_listbox.yview)
        selected_models_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.selected_models_listbox.config(yscrollcommand=selected_models_scrollbar.set)
        for model in self.current_ai_models: self.selected_models_listbox.insert(tk.END, model)

        def add_model_to_list(model_name):
            model_name = model_name.strip()
            if not model_name or model_name in self.selected_models_listbox.get(0, tk.END): return
            if self.selected_models_listbox.size() >= 2:
                messagebox.showwarning("Limit Exceeded", "Max 2 models.", parent=dialog)
                return
            self.selected_models_listbox.insert(tk.END, model_name)

        def remove_selected_model():
            selection = self.selected_models_listbox.curselection()
            if selection: self.selected_models_listbox.delete(selection[0])

        listbox_buttons_frame = tk.Frame(main_frame)
        listbox_buttons_frame.pack(fill=tk.X, pady=(5, 10))
        tk.Button(listbox_buttons_frame, text="Remove Selected", command=remove_selected_model).pack(side=tk.RIGHT)

        models_frame = tk.Frame(main_frame)
        models_frame.pack(fill=tk.X)
        common_models = ["Babelscape/wikineural-multilingual-ner", "dslim/bert-base-NER", "magistermilitum/roberta-multilingual-medieval-ner"]
        model_var = tk.StringVar(value=common_models[0])
        model_combo = ttk.Combobox(models_frame, textvariable=model_var, values=common_models, state="readonly")
        model_combo.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=(0,5))
        tk.Button(models_frame, text="Add Pre-trained", command=lambda: add_model_to_list(model_var.get())).pack(side=tk.LEFT)

        custom_model_frame = tk.Frame(main_frame)
        custom_model_frame.pack(fill=tk.X, pady=(5, 10))
        custom_model_var = tk.StringVar(value="")
        custom_model_entry = tk.Entry(custom_model_frame, textvariable=custom_model_var)
        custom_model_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0,5))
        tk.Button(custom_model_frame, text="Add Custom (HF)", command=lambda: add_model_to_list(custom_model_var.get())).pack(side=tk.LEFT)

        tk.Label(main_frame, text="2. Confidence Score Band:", font=('TkDefaultFont', 10, 'bold')).pack(anchor=tk.W, pady=(10, 5))
        conf_frame = tk.Frame(main_frame)
        conf_frame.pack(fill=tk.X)

        tk.Label(conf_frame, text="Min:").pack(side=tk.LEFT)
        min_conf_var = tk.DoubleVar(value=self.ai_min_conf)
        tk.Scale(conf_frame, variable=min_conf_var, from_=0.0, to=1.0, resolution=0.01, orient=tk.HORIZONTAL).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 10))

        tk.Label(conf_frame, text="Max:").pack(side=tk.LEFT)
        max_conf_var = tk.DoubleVar(value=self.ai_max_conf)
        tk.Scale(conf_frame, variable=max_conf_var, from_=0.0, to=1.0, resolution=0.01, orient=tk.HORIZONTAL).pack(side=tk.LEFT, fill=tk.X, expand=True)

        tk.Label(main_frame, text="3. Map AI Labels to Your Tags:", font=('TkDefaultFont', 10, 'bold')).pack(anchor=tk.W, pady=(15, 5))

        mapping_outer_frame = tk.Frame(main_frame)
        mapping_outer_frame.pack(fill=tk.BOTH, expand=True)  # expand=True allows it to fill the space

        mapping_canvas = tk.Canvas(mapping_outer_frame, highlightthickness=0)
        mapping_scrollbar = ttk.Scrollbar(mapping_outer_frame, orient=tk.VERTICAL, command=mapping_canvas.yview)
        mapping_frame = tk.Frame(mapping_canvas)

        mapping_frame.bind(
            "<Configure>",
            lambda e: mapping_canvas.configure(scrollregion=mapping_canvas.bbox("all"))
        )

        mapping_canvas.create_window((0, 0), window=mapping_frame, anchor="nw")
        mapping_canvas.configure(yscrollcommand=mapping_scrollbar.set)

        mapping_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        mapping_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        def _on_mousewheel(event):
            mapping_canvas.yview_scroll(int(-1*(event.delta/120)), "units")
        mapping_canvas.bind('<Enter>', lambda e: mapping_canvas.bind_all("<MouseWheel>", _on_mousewheel))
        mapping_canvas.bind('<Leave>', lambda e: mapping_canvas.unbind_all("<MouseWheel>"))
        # ----------------------------------------

        standard_ai_labels = [
            "PER", "ACTOR", "TITLE", "REL", "LOC", "INS", "NAT", "EST",
            "PROP", "LEG", "TRANS", "TIM", "DAT", "MON", "TAX", "COM",
            "NUM", "MEA", "RELIC"
        ]
        mapping_vars = {}
        active_tags = ["-- Ignore --"] + self.get_active_tags()

        for ai_lbl in standard_ai_labels:
            row = tk.Frame(mapping_frame)
            row.pack(fill=tk.X, pady=2)
            tk.Label(row, text=f"AI '{ai_lbl}' ➔ ", width=18, anchor=tk.E).pack(side=tk.LEFT)
            var = tk.StringVar()

            if ai_lbl in self.ai_label_mapping:
                guessed = self.ai_label_mapping[ai_lbl]
                if guessed not in active_tags: guessed = "-- Ignore --"
            else:
                guessed = "-- Ignore --"
                if ai_lbl in active_tags: guessed = ai_lbl
                elif ai_lbl == "ORG" and "INS" in active_tags: guessed = "INS"
                elif ai_lbl == "DATE" and "DAT" in active_tags: guessed = "DAT"

            var.set(guessed)
            mapping_vars[ai_lbl] = var
            ttk.Combobox(row, textvariable=var, values=active_tags, state="readonly", width=20).pack(side=tk.LEFT, padx=5)

        row_other = tk.Frame(mapping_frame)
        row_other.pack(fill=tk.X, pady=2)
        tk.Label(row_other, text="Any Other ➔ ", width=18, anchor=tk.E).pack(side=tk.LEFT)

        saved_other = self.ai_label_mapping.get("*", "-- Ignore --")
        if saved_other not in active_tags: saved_other = "-- Ignore --"
        var_other = tk.StringVar(value=saved_other)

        mapping_vars["*"] = var_other
        ttk.Combobox(row_other, textvariable=var_other, values=active_tags, state="readonly", width=20).pack(side=tk.LEFT, padx=5)

        def on_start_annotate():
            model_names = list(self.selected_models_listbox.get(0, tk.END))
            if not model_names: return

            self.ai_min_conf = min_conf_var.get()
            self.ai_max_conf = max_conf_var.get()
            self.ai_label_mapping = {ai_lbl: var.get() for ai_lbl, var in mapping_vars.items()}

            dialog.destroy()
            self._set_ai_models(model_names)
            self._start_ai_annotation_process(model_names, self.ai_label_mapping, self.ai_min_conf, self.ai_max_conf)

        btn_frame = tk.Frame(main_frame)
        btn_frame.pack(fill=tk.X, pady=(20, 0), side=tk.BOTTOM)
        tk.Button(btn_frame, text="Run Hybrid Ensemble", command=on_start_annotate, bg="lightblue").pack(side=tk.RIGHT, padx=5)
        tk.Button(btn_frame, text="Cancel", command=dialog.destroy).pack(side=tk.RIGHT)
        dialog.wait_window()

    def _set_ai_models(self, model_names):
        self.current_ai_models = model_names
        for name in model_names:
            if name in self.last_used_ai_models: self.last_used_ai_models.remove(name)
            self.last_used_ai_models.insert(0, name)
        self.last_used_ai_models = self.last_used_ai_models[:5]

    def _start_ai_annotation_process(self, model_names, label_mapping=None, min_conf=None, max_conf=None):
        if self._is_annotating_ai: return
        self._is_annotating_ai = True
        try: self.settings_menu.entryconfig("Pre-annotate with Hybrid AI...", state="disabled")
        except: pass

        full_text = self.text_area.get("1.0", tk.END)

        if min_conf is None: min_conf = self.ai_min_conf
        if max_conf is None: max_conf = self.ai_max_conf

        if label_mapping is None:
            if self.ai_label_mapping:
                label_mapping = self.ai_label_mapping
            else:
                active = self.get_active_tags()
                # Automatically map HF labels to program labels 1:1 if active
                standard_hf_labels = [
                    "PER", "ACTOR", "TITLE", "REL", "LOC", "INS", "NAT", "EST",
                    "PROP", "LEG", "TRANS", "TIM", "DAT", "MON", "TAX", "COM",
                    "NUM", "MEA", "RELIC"
                ]
                label_mapping = {tag: tag if tag in active else "-- Ignore --" for tag in standard_hf_labels}
                label_mapping["*"] = "-- Ignore --"

        try:
            from transformers import pipeline, AutoTokenizer
            def thread_target():
                try:
                    self._update_status_threadsafe("1/2: Session Memory (Knowledge Base) processing...")
                    memory_anns = self._get_memory_predictions(full_text)

                    pipelines = []
                    for i, model_name in enumerate(model_names):
                        self._update_status_threadsafe(f"2/2: Loading AI model '{model_name}' ({i + 1}/{len(model_names)})...")
                        tokenizer = AutoTokenizer.from_pretrained(model_name)
                        try:
                            if torch.cuda.is_available():
                                ner_pipeline = pipeline("token-classification", model=model_name, tokenizer=tokenizer, aggregation_strategy="max", device="cuda")
                            else:
                                raise RuntimeError("CUDA not available")
                        except (RuntimeError, torch.cuda.OutOfMemoryError) as e:
                            self._update_status_threadsafe(f"CUDA unavailable ({str(e)}), switching to CPU...")
                            ner_pipeline = pipeline("token-classification", model=model_name, tokenizer=tokenizer, aggregation_strategy="max", device="cpu")
                        pipelines.append(ner_pipeline)

                    self._update_status_threadsafe("AI models loaded. Annotating text...")
                    ai_anns = self._get_ai_predictions(full_text, pipelines, label_mapping, min_conf, max_conf)

                    self.root.after(0, self._apply_ensemble_to_ui, memory_anns, ai_anns)

                except Exception as e:
                    self._update_status_threadsafe(f"DONE|Error: {e}")
                    traceback.print_exc()

            threading.Thread(target=thread_target, daemon=True).start()

        except Exception as e:
            self._update_status_threadsafe(f"DONE|Failed to start AI: {e}")
            messagebox.showerror("Error", f"Failed to start AI:\n{e}", parent=self.root)

    def _get_ai_predictions(self, full_text, pipelines, label_mapping, min_conf, max_conf):
        """Extracts AI predictions using a safer, word-based chunking approach to avoid token limits."""
        try:
            all_detected_entities = []

            line_starts = [0]
            for i, char in enumerate(full_text):
                if char == '\n': line_starts.append(i + 1)
            line_starts.append(len(full_text) + 1)

            def offset_to_tkinter(offset):
                line_idx = bisect_right(line_starts, offset) - 1
                line = line_idx + 1
                char = offset - line_starts[line_idx]
                return f"{line}.{char}"

            def find_start_of_word(text, offset):
                while offset > 0 and text[offset-1].isalnum(): offset -= 1
                return offset

            def find_end_of_word(text, offset):
                while offset < len(text) and text[offset].isalnum(): offset += 1
                return offset

            def process_entity_chunk(entity, start_offset_raw, end_offset_raw):
                score = entity.get("score", 1.0)
                if score < min_conf or score > max_conf: return None

                raw_lbl = entity.get("entity_group", "") or entity.get("entity", "")
                base_lbl = raw_lbl[2:] if raw_lbl.startswith(("B-", "I-")) else raw_lbl
                tag = label_mapping.get(base_lbl)

                if not tag: tag = label_mapping.get("*", "-- Ignore --")
                if tag == "-- Ignore --" or tag not in self.entity_tags: return None

                entity_text_raw = full_text[start_offset_raw:end_offset_raw]
                lstrip_len = len(entity_text_raw) - len(entity_text_raw.lstrip())
                rstrip_len = len(entity_text_raw) - len(entity_text_raw.rstrip())
                start_offset_clean = start_offset_raw + lstrip_len
                end_offset_clean = end_offset_raw - rstrip_len

                if self.extend_to_word.get():
                    start_offset_clean = find_start_of_word(full_text, start_offset_clean)
                    end_offset_clean = find_end_of_word(full_text, end_offset_clean)

                final_word = full_text[start_offset_clean:end_offset_clean]
                if not final_word.strip(): return None

                start_pos = offset_to_tkinter(start_offset_clean)
                end_pos = offset_to_tkinter(end_offset_clean)
                start_l, start_c = map(int, start_pos.split("."))
                end_l, end_c = map(int, end_pos.split("."))

                return {"id": uuid.uuid4().hex, "start_line": start_l, "start_char": start_c,
                        "end_line": end_l, "end_char": end_c, "text": final_word, "tag": tag,
                        "propagated": True, "score": float(score)}

            # Find word boundaries in the text to chunk safely without cutting words in half
            word_spans = []
            for match in re.finditer(r'\S+', full_text):
                word_spans.append(match.span())

            chunk_size_words = 150 # Safe number of words to avoid 512 token limit
            overlap_words = 40
            chunks = []

            i = 0
            while i < len(word_spans):
                chunk_spans = word_spans[i : i + chunk_size_words]
                if not chunk_spans: break

                chunk_start = chunk_spans[0][0]
                chunk_end = chunk_spans[-1][1]

                chunks.append((chunk_start, chunk_end, full_text[chunk_start:chunk_end]))

                if i + chunk_size_words >= len(word_spans): break
                i += (chunk_size_words - overlap_words)

            for m_idx, ner_pipeline in enumerate(pipelines):
                for c_idx, (chunk_start, chunk_end, chunk_text) in enumerate(chunks):
                    self._update_status_threadsafe(f"Model {m_idx+1}/{len(pipelines)}: Annotating chunk {c_idx+1}/{len(chunks)}...")

                    if not chunk_text.strip(): continue

                    try:
                        chunk_results = ner_pipeline(chunk_text)
                        for entity in chunk_results:
                            abs_start = chunk_start + entity['start']
                            abs_end = chunk_start + entity['end']
                            new_ann = process_entity_chunk(entity, abs_start, abs_end)
                            if new_ann: all_detected_entities.append(new_ann)

                    except Exception as e:
                        print(f"Warning on chunk {c_idx+1}: {e}")

            unique_annotations = {(ann['start_line'], ann['start_char'], ann['end_line'], ann['end_char'], ann['tag']): ann for ann in all_detected_entities}
            return list(unique_annotations.values())

        except Exception as e:
            print(f"Prediction logic error: {e}")
            traceback.print_exc()
            return []
