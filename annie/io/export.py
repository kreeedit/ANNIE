# -*- coding: utf-8 -*-
import tkinter as tk
from tkinter import filedialog
from tkinter import messagebox
import json
import re
import traceback
import os

class ExportMixin:
    """Annotation / dictionary export."""

    def export_annotations(self):
        if not self.annotations or all(not data.get('entities') for data in self.annotations.values()):
            messagebox.showinfo("Info", "There are no annotations to export.", parent=self.root)
            return
        save_path = filedialog.asksaveasfilename(
            title="Export Annotations for Training",
            initialdir=os.path.dirname(self.files_list[0]) if self.files_list else "",
            filetypes=[("CoNLL Files", "*.conll"), ("spaCy JSONL Files", "*.jsonl"), ("All files", "*.*")],
            parent=self.root)
        if not save_path: return
        try:
            if save_path.lower().endswith(".conll"): self._export_as_conll(save_path)
            elif save_path.lower().endswith(".jsonl"): self._export_as_spacy_jsonl(save_path)
            else:
                messagebox.showwarning("Unknown Format", "File was saved with an unknown extension. Please use '.conll' or '.jsonl'.", parent=self.root)
                return
            messagebox.showinfo("Success", f"Annotations successfully exported to:\n{os.path.basename(save_path)}", parent=self.root)
            self.status_var.set(f"Exported annotations to {os.path.basename(save_path)}")
        except Exception as e:
            messagebox.showerror("Export Error", f"An error occurred during export:\n{e}", parent=self.root)
            traceback.print_exc()

    def export_dictionary(self):
        if not self.annotations:
            messagebox.showinfo("Info", "No annotations in the session.", parent=self.root)
            return

        used_tags = set()
        for fp, data in self.annotations.items():
            for ann in data.get('entities', []):
                used_tags.add(ann['tag'])

        if not used_tags:
            messagebox.showinfo("Info", "No extractable entities found.", parent=self.root)
            return

        dialog = tk.Toplevel(self.root)
        dialog.title("Export Dictionary")
        dialog.geometry("350x450")
        dialog.transient(self.root)
        dialog.grab_set()

        tk.Label(dialog, text="Select tags to export:", font=('TkDefaultFont', 10, 'bold')).pack(pady=(10, 5))

        list_frame = tk.Frame(dialog)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=20)

        scrollbar = tk.Scrollbar(list_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        listbox = tk.Listbox(list_frame, selectmode=tk.MULTIPLE, yscrollcommand=scrollbar.set)
        listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.config(command=listbox.yview)

        sorted_tags = sorted(list(used_tags), key=str.lower)
        for tag in sorted_tags:
            listbox.insert(tk.END, tag)

        listbox.select_set(0, tk.END)

        btn_frame_top = tk.Frame(dialog)
        btn_frame_top.pack(fill=tk.X, padx=20, pady=5)
        tk.Button(btn_frame_top, text="Select all", command=lambda: listbox.select_set(0, tk.END)).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=(0, 2))
        tk.Button(btn_frame_top, text="Clear selection", command=lambda: listbox.selection_clear(0, tk.END)).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=(2, 0))

        def do_export():
            selected_indices = listbox.curselection()
            if not selected_indices:
                messagebox.showwarning("Warning", "No tag selected!", parent=dialog)
                return

            selected_tags = set(listbox.get(i) for i in selected_indices)

            save_path = filedialog.asksaveasfilename(
                title="Save Dictionary",
                defaultextension=".txt",
                filetypes=[("Text Dictionary", "*.txt"), ("All files", "*.*")],
                parent=dialog
            )

            if not save_path:
                return

            unique_entities = set()
            for fp, data in self.annotations.items():
                for ann in data.get('entities', []):
                    if ann['tag'] in selected_tags:
                        txt = ann['text'].strip()
                        txt = txt.replace('\n', ' ').replace('\r', '').replace('\t', ' ')
                        if txt:
                            unique_entities.add((txt, ann['tag']))

            try:
                with open(save_path, 'w', encoding='utf-8') as f:
                    for txt, tag in sorted(unique_entities, key=lambda x: (x[1], x[0].lower())):
                        f.write(f"{txt}\t{tag}\n")

                self.status_var.set(f"Dictionary ({len(unique_entities)} entities) exported: {os.path.basename(save_path)}")
                messagebox.showinfo("Success", f"Saved {len(unique_entities)} unique entities!", parent=dialog)
                dialog.destroy()
            except Exception as e:
                messagebox.showerror("Error", f"Failed to save file:\n{e}", parent=dialog)

        btn_frame_bottom = tk.Frame(dialog)
        btn_frame_bottom.pack(fill=tk.X, padx=20, pady=(10, 20))
        tk.Button(btn_frame_bottom, text="Export", command=do_export, bg="lightblue", width=12).pack(side=tk.RIGHT, padx=(5, 0))
        tk.Button(btn_frame_bottom, text="Cancel", command=dialog.destroy, width=8).pack(side=tk.RIGHT)

    def _export_as_spacy_jsonl(self, save_path):
        with open(save_path, 'w', encoding='utf-8') as f:
            for file_path, data in self.annotations.items():
                if not data.get("entities"): continue

                try:
                    with open(file_path, 'r', encoding='utf-8') as text_file:
                        content = text_file.read()
                except Exception:
                    continue

                raw_spans = []
                sorted_entities = sorted(data['entities'], key=lambda x: (x['start_line'], x['start_char']))

                for ann in sorted_entities:
                    start_char = self._tkinter_index_to_char_offset(content, ann['start_line'], ann['start_char'])
                    end_char = self._tkinter_index_to_char_offset(content, ann['end_line'], ann['end_char'])
                    raw_spans.append({"start": start_char, "end": end_char, "label": ann['tag']})

                normalized_text, remapped_spans = self._normalize_and_remap(content, raw_spans)

                spacy_doc = {"text": normalized_text, "spans": remapped_spans}
                f.write(json.dumps(spacy_doc, ensure_ascii=False) + '\n')

    def _export_as_conll(self, save_path):
        with open(save_path, 'w', encoding='utf-8') as f:
            for file_path, data in self.annotations.items():
                if not data.get("entities"): continue

                try:
                    with open(file_path, 'r', encoding='utf-8') as text_file:
                        content = text_file.read()
                except Exception:
                    continue

                raw_spans = []
                sorted_entities = sorted(data['entities'], key=lambda x: (x['start_line'], x['start_char']))

                for ann in sorted_entities:
                    start_char = self._tkinter_index_to_char_offset(content, ann['start_line'], ann['start_char'])
                    end_char = self._tkinter_index_to_char_offset(content, ann['end_line'], ann['end_char'])
                    raw_spans.append({"start": start_char, "end": end_char, "label": ann['tag']})

                normalized_text, remapped_spans = self._normalize_and_remap(content, raw_spans)

                tokens = [(m.group(0), m.start()) for m in re.finditer(r'\w+|[^\w\s]', normalized_text)]
                tags = ["O"] * len(tokens)

                for span in remapped_spans:
                    start_char_abs = span['start']
                    end_char_abs = span['end']
                    tag_name = span['label']

                    is_first_token = True
                    for i, (token_text, token_start) in enumerate(tokens):
                        token_end = token_start + len(token_text)

                        if token_start >= start_char_abs and token_end <= end_char_abs:
                            if is_first_token:
                                tags[i] = f"B-{tag_name}"
                                is_first_token = False
                            else:
                                tags[i] = f"I-{tag_name}"

                for i, (token_text, _) in enumerate(tokens):
                    f.write(f"{token_text} {tags[i]}\n")
                f.write("\n")

    def _ask_for_save_directory(self, initial_dir):
        dialog = tk.Toplevel(self.root)
        dialog.title("Select Save Directory")
        dialog.geometry("500x150")
        dialog.transient(self.root)
        dialog.grab_set()
        result = {"path": ""}
        tk.Label(dialog, text="Choose a directory to save the imported files into.").pack(pady=10)
        entry_frame = tk.Frame(dialog)
        entry_frame.pack(fill=tk.X, padx=10)
        path_var = tk.StringVar(value=initial_dir)
        entry = tk.Entry(entry_frame, textvariable=path_var)
        entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        def browse():
            dir_path = filedialog.askdirectory(initialdir=path_var.get(), parent=dialog)
            if dir_path: path_var.set(dir_path)
        tk.Button(entry_frame, text="Browse...", command=browse).pack(side=tk.LEFT, padx=(5,0))
        btn_frame = tk.Frame(dialog)
        btn_frame.pack(pady=10)
        def on_ok():
            result["path"] = path_var.get()
            dialog.destroy()
        def on_cancel():
            result["path"] = ""
            dialog.destroy()
        tk.Button(btn_frame, text="OK", width=10, command=on_ok).pack(side=tk.LEFT, padx=5)
        tk.Button(btn_frame, text="Cancel", width=10, command=on_cancel).pack(side=tk.LEFT, padx=5)
        self.root.wait_window(dialog)
        return result["path"]
