# -*- coding: utf-8 -*-
import tkinter as tk
from tkinter import filedialog
from tkinter import messagebox
import uuid
import re
import os

class PropagationMixin:
    """Dictionary propagation of annotations."""

    def propagate_annotations(self):
        if not self.current_file_path: return
        source_entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        if not source_entities: return
        allowed_tags = {tag for tag, allowed in self.tag_propagation_states.items() if allowed}
        filtered_entities = [ann for ann in source_entities if ann['tag'] in allowed_tags]
        if not filtered_entities: return
        text_to_tag = {ann['text'].strip(): ann['tag'] for ann in sorted(filtered_entities, key=lambda a: (a['start_line'], a['start_char'])) if ann['text'].strip()}
        if not text_to_tag: return

        self._show_propagation_scope_dialog(text_to_tag)

    def _show_propagation_scope_dialog(self, text_to_tag):
        dialog = tk.Toplevel(self.root)
        dialog.title("Propagation scope")
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.resizable(False, False)

        main_frame = tk.Frame(dialog, padx=20, pady=15)
        main_frame.pack(fill="both", expand=True)
        tk.Label(main_frame,
                 text=f"Propagate {len(text_to_tag)} unique entit{'y' if len(text_to_tag) == 1 else 'ies'}.\nWhere do you want to search?",
                 justify=tk.CENTER).pack(pady=(0, 15))

        btn_frame = tk.Frame(main_frame)
        btn_frame.pack(fill=tk.X)

        def choose_current():
            dialog.destroy()
            self._perform_propagation(text_to_tag, "Current File Propagation", target_files=[self.current_file_path])

        def choose_all():
            dialog.destroy()
            self._perform_propagation(text_to_tag, "Current File Propagation", target_files=None)

        current_btn = tk.Button(btn_frame, text="Current File", command=choose_current, width=14)
        current_btn.pack(side=tk.LEFT, padx=(0, 10))

        all_btn = tk.Button(btn_frame, text="All Files", command=choose_all, width=14, default=tk.ACTIVE)
        all_btn.pack(side=tk.LEFT)

        dialog.protocol("WM_DELETE_WINDOW", lambda: None)
        dialog.bind('<Return>', lambda event: all_btn.invoke())
        dialog.bind('<Escape>', lambda event: current_btn.invoke())

        self.root.update_idletasks()
        x = self.root.winfo_x() + (self.root.winfo_width() - dialog.winfo_reqwidth()) / 2
        y = self.root.winfo_y() + (self.root.winfo_height() - dialog.winfo_reqheight()) / 2
        dialog.geometry(f"+{int(x)}+{int(y)}")
        all_btn.focus_set()

    def load_and_propagate_from_dictionary(self):
        if not self.files_list: return
        dict_path = filedialog.askopenfilename(title="Select Dictionary File", filetypes=[("Text files", "*.txt"), ("All files", "*.*")])
        if not dict_path: return
        dictionary_mapping = {}
        missing_tags = set()
        try:
            with open(dict_path, 'r', encoding='utf-8') as f:
                for line in f:
                    if line.strip() and not line.startswith('#'):
                        parts = line.strip().rsplit(None, 1)
                        if len(parts) == 2:
                            term, tag = parts[0].strip(), parts[1].strip()
                            dictionary_mapping[term] = tag
                            if tag not in self.entity_tags: missing_tags.add(tag)
        except Exception as e:
            messagebox.showerror("Dict Read Error", f"Failed to read dictionary:\n{e}", parent=self.root)
            return

        if missing_tags:
            msg = (f"The dictionary contains new tags:\n\n{', '.join(missing_tags)}\n\nAdd them to the session?")
            if messagebox.askyesno("Adding new tags", msg, parent=self.root):
                if "Dictionary Layer" not in self.tag_hierarchy: self.tag_hierarchy["Dictionary Layer"] = []
                for t in missing_tags:
                    if t not in self.entity_tags:
                        self.tag_hierarchy["Dictionary Layer"].append(t)
                        self.tag_active_states[t] = True
                        self.tag_propagation_states[t] = True
                self._sync_flat_tags()
                self._update_entity_tag_combobox()
                self._configure_text_tags()
            else:
                dictionary_mapping = {k: v for k, v in dictionary_mapping.items() if v not in missing_tags}

        if not dictionary_mapping: return
        self._show_dictionary_propagation_dialog(dictionary_mapping)

    def _show_dictionary_propagation_dialog(self, dictionary_mapping):
        dialog = tk.Toplevel(self.root)
        dialog.title("Target files of propagation")
        dialog.geometry("450x500")
        dialog.transient(self.root)
        dialog.grab_set()

        tk.Label(dialog, text=f"The dictionary contains {len(dictionary_mapping)} entities.\nSelect which files to search:", font=('TkDefaultFont', 10, 'bold'), justify=tk.LEFT).pack(pady=(10, 5), padx=20, anchor=tk.W)

        list_frame = tk.Frame(dialog)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=20)

        scrollbar = tk.Scrollbar(list_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        listbox = tk.Listbox(list_frame, selectmode=tk.MULTIPLE, yscrollcommand=scrollbar.set)
        listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.config(command=listbox.yview)

        for file_path in self.files_list:
            display_name = os.path.basename(file_path)
            listbox.insert(tk.END, display_name)

        listbox.select_set(0, tk.END)

        btn_frame_top = tk.Frame(dialog)
        btn_frame_top.pack(fill=tk.X, padx=20, pady=5)
        tk.Button(btn_frame_top, text="Select all", command=lambda: listbox.select_set(0, tk.END)).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=(0, 2))
        tk.Button(btn_frame_top, text="Delete selection", command=lambda: listbox.selection_clear(0, tk.END)).pack(side=tk.LEFT, expand=True, fill=tk.X, padx=(2, 0))

        def do_propagate():
            selected_indices = listbox.curselection()
            if not selected_indices:
                messagebox.showwarning("Warning!", "No selection made!", parent=dialog)
                return

            selected_files = [self.files_list[i] for i in selected_indices]
            dialog.destroy()

            self._perform_propagation(dictionary_mapping, "Dictionary Propagation", target_files=selected_files)

        btn_frame_bottom = tk.Frame(dialog)
        btn_frame_bottom.pack(fill=tk.X, padx=20, pady=(10, 20))
        tk.Button(btn_frame_bottom, text="Propagate", command=do_propagate, bg="lightblue", width=16).pack(side=tk.RIGHT, padx=(5, 0))
        tk.Button(btn_frame_bottom, text="Cancel", command=dialog.destroy, width=8).pack(side=tk.RIGHT)

    def _perform_propagation(self, text_to_tag_map, source_description, target_files=None):
        if target_files is None:
            target_files = self.files_list

        propagated_count, affected_files = 0, set()
        allow_overlap = True if "Dictionary" in source_description else self.allow_multilabel_overlap.get()
        self.status_var.set(f"Starting {source_description}..."); self.root.update()
        file_contents = {}

        for file_path in target_files:
            try:
                with open(file_path, 'r', encoding='utf-8') as f: file_contents[file_path] = f.read()
            except Exception: continue

        compiled_regexes = []
        for text, tag in text_to_tag_map.items():
            # Only use word boundary (\b) when the adjacent character is a
            # word character (\w).  The trailing \b would NEVER match when
            # the search text ends with punctuation, parentheses, or other
            # non-alphanumeric characters (e.g. "Ego Iohannes notarius
            # interfui. (S)").
            #
            # Multi-word formulae use \s+ between tokens so that line breaks,
            # tabs, or multiple spaces in the target text do not prevent a
            # match (e.g. vocabulary "iussu predicti iudicis" matches
            # "iussu\npredicti iudicis" in the file).
            pattern = ''
            if text and text[0].isalnum():
                pattern += r'\b'
            tokens = text.split()
            if len(tokens) == 1:
                pattern += re.escape(text)
            else:
                pattern += r'\s+'.join(re.escape(t) for t in tokens)
            if text and text[-1].isalnum():
                pattern += r'\b'
            compiled_regexes.append((re.compile(pattern, re.IGNORECASE), tag, text))
        compiled_regexes.sort(key=lambda x: len(x[2]), reverse=True)

        for file_path, content in file_contents.items():
            target_entities = self.annotations.setdefault(file_path, {"entities": [], "relations": []})['entities']
            existing_spans_and_tags = {(ann['start_line'], ann['start_char'], ann['end_line'], ann['end_char'], ann['tag']) for ann in target_entities}
            line_starts = [0]
            for i, char in enumerate(content):
                if char == '\n': line_starts.append(i + 1)
            line_starts.append(len(content) + 1)

            for regex, tag, matched_text_original in compiled_regexes:
                for match in regex.finditer(content):
                    matched_text = re.sub(r'\s+', ' ', match.group()).strip()
                    start_index, end_index = match.span()
                    start_pos = self._char_offset_to_tkinter_index_from_offsets(line_starts, start_index)
                    end_pos = self._char_offset_to_tkinter_index_from_offsets(line_starts, end_index)
                    start_l, start_c = map(int, start_pos.split('.'))
                    end_l, end_c = map(int, end_pos.split('.'))
                    current_span_and_tag = (start_l, start_c, end_l, end_c, tag)

                    if current_span_and_tag in existing_spans_and_tags: continue
                    if not allow_overlap and self._is_overlapping_in_list(start_l, start_c, end_l, end_c, target_entities): continue

                    new_ann = {'id': uuid.uuid4().hex, 'start_line': start_l, 'start_char': start_c,
                               'end_line': end_l, 'end_char': end_c, 'text': matched_text, 'tag': tag, 'propagated': True}
                    target_entities.append(new_ann)
                    existing_spans_and_tags.add(current_span_and_tag)
                    propagated_count += 1
                    affected_files.add(file_path)

        if self.current_file_path in affected_files:
            self._build_entity_lookup_map(self.annotations.get(self.current_file_path, {})['entities'])
            self.update_entities_list()
            self.apply_annotations_to_text()
        self._update_button_states()
        self.status_var.set(f"{source_description} complete. Added {propagated_count} entities across {len(affected_files)} files.")
