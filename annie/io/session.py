# -*- coding: utf-8 -*-
import tkinter as tk
from tkinter import filedialog
from tkinter import messagebox
import json
import traceback
import os
from annie.constants import SESSION_FILE_VERSION

class SessionMixin:
    """Save/load session + schema + lifecycle."""

    def save_schema(self):
        save_path = filedialog.asksaveasfilename(
            title="Save Tag/Relation Schema",
            defaultextension=".json",
            filetypes=[("ANNIE Schema Files", "*.json"), ("All files", "*.*")],
            parent=self.root)
        if not save_path: return
        schema_data = {
            "tag_hierarchy": self.tag_hierarchy,
            "tag_active_states": self.tag_active_states,
            "relation_types": self.relation_types
        }
        try:
            with open(save_path, 'w', encoding='utf-8') as f: json.dump(schema_data, f, indent=2)
            self.status_var.set(f"Schema saved to {os.path.basename(save_path)}")
        except Exception as e:
            messagebox.showerror("Save Error", f"Could not save schema file:\n{e}", parent=self.root)

    def load_schema(self):
        if self.annotations and not messagebox.askyesno("Confirm Load", "Loading a new schema will replace your current tags. This may affect existing annotations if the tags don't match.\n\nContinue?"): return
        load_path = filedialog.askopenfilename(
            title="Load Tag/Relation Schema",
            filetypes=[("ANNIE Schema Files", "*.json"), ("All files", "*.*")],
            parent=self.root)
        if not load_path: return
        try:
            with open(load_path, 'r', encoding='utf-8') as f: schema_data = json.load(f)

            if "tag_hierarchy" in schema_data:
                self.tag_hierarchy = schema_data["tag_hierarchy"]
                self.tag_active_states = schema_data.get("tag_active_states", {})
            elif "entity_tags" in schema_data:
                self.tag_hierarchy = {"Imported Schema": schema_data["entity_tags"]}
                self.tag_active_states = {t: True for t in schema_data["entity_tags"]}
            else:
                raise ValueError("File is not a valid schema file.")

            self.relation_types = schema_data.get("relation_types", [])
            self._sync_flat_tags()

            self._update_entity_tag_combobox()
            self._update_relation_type_combobox()
            self._ensure_default_colors()
            self._configure_text_tags()
            if self.current_file_path:
                self.apply_annotations_to_text()
                self.update_entities_list()
                self.update_relations_list()
            self.status_var.set(f"Successfully loaded schema from {os.path.basename(load_path)}")
        except Exception as e:
            messagebox.showerror("Load Error", f"Could not load schema file:\n{e}", parent=self.root)

    def save_annotations(self):
        if not self.annotations or all(not data.get('entities') and not data.get('relations') for data in self.annotations.values()):
            messagebox.showinfo("Info", "There are no annotations to save.", parent=self.root)
            return
        initial_dir = os.path.dirname(self.files_list[0]) if self.files_list else ""
        save_path = filedialog.asksaveasfilename(
            initialdir=initial_dir, initialfile="annotations.json", defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")], parent=self.root)
        if not save_path: return
        save_dir = os.path.dirname(save_path)
        serializable_annotations = {}
        for file_path, data in self.annotations.items():
            if not data.get("entities") and not data.get("relations"): continue
            try:
                rel_path = os.path.relpath(file_path, start=save_dir)
                key = rel_path.replace('\\', '/') if not rel_path.startswith('..') else os.path.basename(file_path)
            except ValueError:
                key = os.path.basename(file_path)
            serializable_annotations[key] = {
                "entities": sorted(data.get("entities", []), key=lambda a: (a['start_line'], a['start_char'])),
                "relations": sorted(data.get("relations", []), key=lambda r: (r.get('type', ''), r.get('head_id', '')))
            }
        try:
            with open(save_path, 'w', encoding='utf-8') as f: json.dump(serializable_annotations, f, indent=2, ensure_ascii=False)
            self.status_var.set(f"Annotations saved to '{os.path.basename(save_path)}'")
        except Exception as e:
            messagebox.showerror("Save Error", f"Could not write annotations to file:\n{e}", parent=self.root)

    def save_session(self, force_ask=False):
        if not self.files_list:
            messagebox.showwarning("Cannot Save Session", "Please open a directory first.", parent=self.root)
            return
        save_path = self.session_save_path
        if force_ask or not save_path:
            initial_dir = os.path.dirname(self.files_list[0])
            dir_name = os.path.basename(initial_dir)
            save_path = filedialog.asksaveasfilename(
                initialdir=initial_dir, initialfile=f"{dir_name}_session.json", defaultextension=".json",
                filetypes=[("ANNIE Session files", "*.json"), ("All files", "*.*")], parent=self.root)
        if not save_path:
            self.status_var.set("Save session cancelled.")
            return

        session_data = {
            "version": SESSION_FILE_VERSION,
            "files_list": self.files_list,
            "current_file_index": self.current_file_index,
            "tag_hierarchy": self.tag_hierarchy,
            "tag_active_states": self.tag_active_states,
            "tag_propagation_states": self.tag_propagation_states,
            "selection_mode": self.selection_mode.get(),
            "relation_types": self.relation_types,
            "tag_colors": self.tag_colors,
            "annotations": self.annotations,
            "extend_to_word": self.extend_to_word.get(),
            "allow_multilabel_overlap": self.allow_multilabel_overlap.get(),
            "last_used_ai_models": self.last_used_ai_models,
            "current_ai_models": self.current_ai_models,
            "ai_min_conf": self.ai_min_conf,
            "ai_max_conf": self.ai_max_conf,
            "ai_label_mapping": self.ai_label_mapping,
            "llm_provider": self.llm_provider,
            "llm_models": self.llm_models,
            "llm_model": self.llm_model,
            "llm_few_shot_count": self.llm_few_shot_count
        }

        try:
            with open(save_path, 'w', encoding='utf-8') as f: json.dump(session_data, f, indent=2, ensure_ascii=False)
            self.session_save_path = save_path
            self.status_var.set(f"Session saved to '{os.path.basename(save_path)}'")
            base_dir_name = os.path.basename(os.path.dirname(self.files_list[0]))
            self.root.title(f"ANNIE - {base_dir_name} [{os.path.basename(save_path)}]")
        except Exception as e:
            messagebox.showerror("Save Session Error", f"Could not write session file:\n{e}", parent=self.root)

    def load_session(self):
        if self._has_unsaved_changes():
            response = messagebox.askyesnocancel("Unsaved Changes", "You have unsaved changes.\nSave before loading session?", parent=self.root)
            if response is True:
                self.save_session()
                if not self.session_save_path: return
            elif response is None: return

        load_path = filedialog.askopenfilename(filetypes=[("ANNIE Session files", "*.json"), ("All files", "*.*")], parent=self.root)
        if not load_path: return

        try:
            with open(load_path, 'r', encoding='utf-8') as f: session_data = json.load(f)
        except Exception as e:
            messagebox.showerror("Load Session Error", f"Could not read session file:\n{e}", parent=self.root)
            return

        required_keys = ["files_list", "annotations", "relation_types"]
        if not all(key in session_data for key in required_keys):
            messagebox.showerror("Load Session Error", "Session file is missing core required data.", parent=self.root)
            return

        if "entity_tags" not in session_data and "tag_hierarchy" not in session_data:
            messagebox.showerror("Load Session Error", "Session file is missing tag definitions.", parent=self.root)
            return

        missing_files = [fp for fp in session_data["files_list"] if not os.path.isfile(fp)]
        if missing_files:
            msg = "Some text files could not be found:\n- " + "\n- ".join(os.path.basename(p) for p in missing_files[:5])
            if len(missing_files) > 5: msg += "\n..."
            if not messagebox.askyesno("Missing Files", f"{msg}\n\nContinue loading session?", parent=self.root): return

        self._reset_state()
        try:
            self.files_list = session_data["files_list"]
            self.annotations = session_data["annotations"]

            if "tag_hierarchy" in session_data:
                self.tag_hierarchy = session_data["tag_hierarchy"]
                self.tag_active_states = session_data.get("tag_active_states", {})
            else:
                old_tags = session_data.get("entity_tags", [])
                self.tag_hierarchy = {"Custom Layer": old_tags}
                self.tag_active_states = {t: True for t in old_tags}

            loaded_states = session_data.get("tag_propagation_states", {})
            self._sync_flat_tags()
            self.tag_propagation_states = {tag: loaded_states.get(tag, True) for tag in self.entity_tags}

            self.selection_mode.set(session_data.get("selection_mode", "word"))
            self.relation_types = session_data["relation_types"]
            self.tag_colors = session_data.get("tag_colors", {})
            self.extend_to_word.set(session_data.get("extend_to_word", False))
            self.allow_multilabel_overlap.set(session_data.get("allow_multilabel_overlap", True))
            self.session_save_path = load_path
            self.last_used_ai_models = session_data.get("last_used_ai_models", [])
            self.current_ai_models = session_data.get("current_ai_models", [])

            self.ai_min_conf = session_data.get("ai_min_conf", 0.60)
            self.ai_max_conf = session_data.get("ai_max_conf", 1.00)
            self.ai_label_mapping = session_data.get("ai_label_mapping", {})

            self.llm_provider = session_data.get("llm_provider", "Anthropic (Claude)")
            self.llm_models = session_data.get("llm_models", {
                "OpenAI": "gpt-4o-mini",
                "Anthropic (Claude)": "claude-sonnet-4-6",
                "Together AI": "meta-llama/Meta-Llama-3.1-8B-Instruct-Turbo",
                "Hugging Face": "HuggingFaceH4/zephyr-7b-alpha"
            })
            self.llm_model = session_data.get("llm_model", self.llm_models.get(self.llm_provider, ""))
            self.hf_api_key = session_data.get("hf_api_key", "")
            self.claude_api_key = session_data.get("claude_api_key", "")
            self.openai_api_key = session_data.get("openai_api_key", "")
            self.together_api_key = session_data.get("together_api_key", "")
            self.llm_few_shot_count = session_data.get("llm_few_shot_count", 3)

            self.files_listbox.delete(0, tk.END)
            for file_path in self.files_list:
                display_name = os.path.basename(file_path)
                if file_path in missing_files: display_name += " [MISSING]"
                self.files_listbox.insert(tk.END, display_name)

            self._update_entity_tag_combobox()
            self._update_relation_type_combobox()
            self._ensure_default_colors()
            self._configure_text_tags()
            self._configure_treeview_tags()

            idx_to_load = session_data.get("current_file_index", 0)
            if self.files_list and 0 <= idx_to_load < len(self.files_list) and self.files_list[idx_to_load] not in missing_files:
                self.load_file(idx_to_load)
            else:
                self.status_var.set("Session loaded. No files to display.")

            base_dir_name = os.path.basename(os.path.dirname(self.files_list[0])) if self.files_list else "Session"
            self.root.title(f"ANNIE - {base_dir_name} [{os.path.basename(load_path)}]")

        except Exception as e:
            messagebox.showerror("Load Session Error", f"Error applying session data:\n{e}", parent=self.root)
            self._reset_state()
            traceback.print_exc()
        finally:
            self._update_button_states()

    def _has_unsaved_changes(self): return bool(self.files_list)

    def _on_closing(self):
        if self._has_unsaved_changes():
            response = messagebox.askyesnocancel("Exit Confirmation", "You have an active session.\nSave before exiting?", parent=self.root)
            if response is True:
                self.save_session()
                if self.session_save_path: self.root.quit()
            elif response is False: self.root.quit()
        else: self.root.quit()
