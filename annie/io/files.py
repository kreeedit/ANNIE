# -*- coding: utf-8 -*-
import tkinter as tk
from tkinter import filedialog
from tkinter import messagebox
import re
import os
import shutil

class FilesMixin:
    """Directory / file / session-file loading."""

    def load_directory(self):
        if self._has_unsaved_changes():
            if not messagebox.askyesno("Unsaved Changes", "You have unsaved changes.\nDiscard and load new directory?", parent=self.root): return
        directory = filedialog.askdirectory(title="Select Directory with Text Files")
        if directory:
            new_files_list = []
            xml_converted = []
            try:
                for filename in sorted(os.listdir(directory)):
                    filepath = os.path.join(directory, filename)
                    if os.path.isfile(filepath):
                        if filename.lower().endswith(".txt"):
                            new_files_list.append(filepath)
                        elif filename.lower().endswith(".xml"):
                            # Convert XML to TXT (if CEI XML)
                            converted_path = self._convert_cei_xml_to_txt(filepath, directory)
                            if converted_path:
                                new_files_list.append(converted_path)
                                xml_converted.append(filename)
            except OSError as e:
                messagebox.showerror("Error Loading Directory", f"Could not read directory contents:\n{e}", parent=self.root)
                return
            if new_files_list:
                self._reset_state()
                self.files_list = new_files_list
                self.files_listbox.delete(0, tk.END)
                for file_path in self.files_list:
                    self.files_listbox.insert(tk.END, os.path.basename(file_path))
                self.load_file(0)
                msg = f"Loaded {len(self.files_list)} files from '{os.path.basename(directory)}'"
                if xml_converted:
                    msg += f" (converted {len(xml_converted)} XML file(s))"
                self.status_var.set(msg)
                self.root.title(f"ANNIE - {os.path.basename(directory)}")
            else:
                self.status_var.set(f"No supported files found in '{os.path.basename(directory)}'")
            self._update_button_states()

    def convert_session_to_sentences(self):
        if not self.files_list:
            messagebox.showwarning("No Data", "Please open a directory or load a session first.", parent=self.root)
            return

        if not messagebox.askyesno("Convert to Sentences",
                                   "This function will split the current documents into sentences.\n"
                                   "Each sentence will become a separate item in the left list, and existing annotations will be recalculated.\n\n"
                                   "The process will save the sentences into a new folder of your choice. Continue?",
                                   parent=self.root): return

        save_dir = filedialog.askdirectory(title="Select a folder to save sentences", parent=self.root)
        if not save_dir: return
        os.makedirs(save_dir, exist_ok=True)

        self.status_var.set("Splitting into sentences and migrating annotations...")
        self.progress_bar.start()
        self.root.update()

        new_files_list = []
        new_annotations = {}

        # ---------------------------------------------------------------------
        # Negative Lookbehind a Regex-ben.
        # A (?<!\b[A-Za-z]\.)
        # (pl. A., F., M., C.)".
        # ---------------------------------------------------------------------
        sentence_end_pattern = re.compile(r'(?<!\b[A-Za-z]\.)(?<=[.!?])\s+|\n+')

        for file_path in self.files_list:
            try:
                with open(file_path, 'r', encoding='utf-8') as f: content = f.read()
            except Exception as e:
                print(f"Error reading file {file_path}: {e}")
                continue

            base_name = os.path.basename(file_path).replace('.txt', '')
            sentences = []
            current_sentence_start = 0

            for match in sentence_end_pattern.finditer(content):
                potential_end = match.end()
                potential_text = content[current_sentence_start:potential_end]
                valid_words = [w for w in potential_text.split() if len(w.replace('.', '').replace(',', '')) > 1]
                word_count = len(valid_words)

                if word_count >= 8 or '\n' in match.group():
                    if potential_text.strip():
                        sentences.append((current_sentence_start, potential_end, potential_text))
                    current_sentence_start = potential_end

            if current_sentence_start < len(content):
                s_text = content[current_sentence_start:]
                if s_text.strip(): sentences.append((current_sentence_start, len(content), s_text))

            file_annotations = self.annotations.get(file_path, {}).get('entities', [])
            file_relations = self.annotations.get(file_path, {}).get('relations', [])

            for i, (s_start, s_end, s_text) in enumerate(sentences):
                if not s_text.strip(): continue
                new_file_name = f"{base_name}_sent_{i+1:04d}.txt"
                new_file_path = os.path.join(save_dir, new_file_name)

                try:
                    with open(new_file_path, 'w', encoding='utf-8') as f: f.write(s_text.strip())
                except Exception as e:
                    print(f"Error writing sentence file {new_file_path}: {e}")
                    continue

                new_files_list.append(new_file_path)
                new_annotations[new_file_path] = {"entities": [], "relations": []}
                sentence_entities = []
                old_id_to_new_id = {}

                for ann in file_annotations:
                    try:
                        ann_start_abs = self._tkinter_index_to_char_offset(content, ann['start_line'], ann['start_char'])
                        ann_end_abs = self._tkinter_index_to_char_offset(content, ann['end_line'], ann['end_char'])
                    except Exception as e:
                        print(f"Skipping malformed annotation {ann.get('id')}: {e}")
                        continue

                    if ann_start_abs >= s_start and ann_end_abs <= s_end:
                        leading_spaces = len(s_text) - len(s_text.lstrip())
                        rel_start = ann_start_abs - s_start - leading_spaces
                        rel_end = ann_end_abs - s_start - leading_spaces
                        clean_s_text = s_text.strip()
                        rel_start = max(0, rel_start)
                        rel_end = min(len(clean_s_text), rel_end)

                        new_line_starts = [0]
                        for j, char in enumerate(clean_s_text):
                            if char == '\n': new_line_starts.append(j + 1)
                        new_line_starts.append(len(clean_s_text) + 1)

                        new_start_pos = self._char_offset_to_tkinter_index_from_offsets(new_line_starts, rel_start)
                        new_end_pos = self._char_offset_to_tkinter_index_from_offsets(new_line_starts, rel_end)

                        try:
                            start_l, start_c = map(int, new_start_pos.split('.'))
                            end_l, end_c = map(int, new_end_pos.split('.'))
                        except ValueError: continue

                        new_ann = {
                            'id': ann['id'], 'start_line': start_l, 'start_char': start_c,
                            'end_line': end_l, 'end_char': end_c, 'text': ann['text'], 'tag': ann['tag']
                        }
                        if 'propagated' in ann: new_ann['propagated'] = ann['propagated']
                        if 'score' in ann: new_ann['score'] = ann['score']

                        sentence_entities.append(new_ann)
                        old_id_to_new_id[ann['id']] = ann['id']

                new_annotations[new_file_path]["entities"] = sentence_entities

                sentence_relations = []
                for rel in file_relations:
                    if rel['head_id'] in old_id_to_new_id and rel['tail_id'] in old_id_to_new_id:
                        sentence_relations.append({
                            'id': rel['id'], 'type': rel['type'], 'head_id': rel['head_id'], 'tail_id': rel['tail_id']
                        })
                new_annotations[new_file_path]["relations"] = sentence_relations

        self._reset_state()
        self.files_list = new_files_list
        self.annotations = new_annotations

        for path in self.files_list:
            self.files_listbox.insert(tk.END, os.path.basename(path))
        if self.files_list: self.load_file(0)
        self.progress_bar.stop()
        self.status_var.set(f"Conversion complete. Generated {len(self.files_list)} sentences for training.")
        messagebox.showinfo("Done", f"Successfully split into {len(self.files_list)} sentences.\nThe left panel now displays sentences instead of whole documents.", parent=self.root)

    def add_files_to_session(self):
        if not self.files_list:
            messagebox.showwarning("No Session Active", "Please open a directory or load a session first.", parent=self.root)
            return
        source_paths = filedialog.askopenfilenames(
            title="Select Text File(s) to Add",
            filetypes=[("Text files", "*.txt"), ("XML Files", "*.xml"), ("All files", "*.*")],
            parent=self.root)
        if not source_paths: return
        destination_dir = os.path.dirname(self.files_list[0])
        current_basenames = {os.path.basename(p) for p in self.files_list}
        added_count = 0
        xml_converted = 0
        for source_path in source_paths:
            basename = os.path.basename(source_path)
            # If xml file, convert to txt
            if basename.lower().endswith(".xml"):
                converted_path = self._convert_cei_xml_to_txt(source_path, destination_dir)
                if converted_path:
                    dest_path = converted_path
                    xml_converted += 1
                else:
                    # Not CEI XML, skip
                    continue
            else:
                dest_path = os.path.join(destination_dir, basename)
                if basename in current_basenames:
                    messagebox.showwarning("File Exists", f"A file named '{basename}' is already in this session. Skipping.", parent=self.root)
                    continue
                if os.path.abspath(source_path) != os.path.abspath(dest_path):
                    try: shutil.copy2(source_path, dest_path)
                    except Exception as e:
                        messagebox.showerror("Copy Error", f"Could not copy file '{basename}'.\n\nError: {e}", parent=self.root)
                        continue
            self.files_list.append(dest_path)
            added_count += 1

        if added_count > 0:
            current_selection_path = self.current_file_path
            self.files_list.sort(key=lambda p: os.path.basename(p).lower())
            self.files_listbox.delete(0, tk.END)
            for path in self.files_list: self.files_listbox.insert(tk.END, os.path.basename(path))
            if current_selection_path in self.files_list:
                new_index = self.files_list.index(current_selection_path)
                self.files_listbox.selection_set(new_index)
                self.files_listbox.see(new_index)
                self.files_listbox.activate(new_index)
            self._update_button_states()
            msg = f"Successfully added {added_count - xml_converted} file(s) and converted {xml_converted} XML file(s) to the session."
            self.status_var.set(msg)

    def load_file(self, index):
        if not (0 <= index < len(self.files_list)): return
        if index == self.current_file_index: return
        self.clear_views()
        self.current_file_index = index
        self.current_file_path = self.files_list[index]
        filename = os.path.basename(self.current_file_path)
        self.files_listbox.selection_clear(0, tk.END)
        self.files_listbox.selection_set(index)
        self.files_listbox.activate(index)
        self.files_listbox.see(index)
        self.text_area.config(state=tk.NORMAL)
        self.text_area.delete(1.0, tk.END)
        try:
            with open(self.current_file_path, 'r', encoding='utf-8') as f:
                file_content = f.read()
                self.text_area.insert(tk.END, file_content)

            self.line_start_offsets = [0]
            for i, char in enumerate(file_content):
                if char == '\n': self.line_start_offsets.append(i + 1)
            self.line_start_offsets.append(len(file_content) + 1)

            file_data = self.annotations.setdefault(self.current_file_path, {"entities": [], "relations": []})
            self._build_entity_lookup_map(file_data.get("entities", []))
            self.update_entities_list()
            self.update_relations_list()
            self.apply_annotations_to_text()
            self.status_var.set(f"Loaded: {filename} ({index + 1}/{len(self.files_list)})")
            self.text_area.edit_reset()
        except Exception as e:
            messagebox.showerror("Error Reading File", f"Failed to load file '{filename}':\n{str(e)}", parent=self.root)
            self.clear_views()
            self.current_file_path = None
            self.status_var.set(f"Error loading {filename}")
        finally:
            self.text_area.config(state=tk.DISABLED)
            self._update_button_states()

    def load_next_file(self):
        if 0 <= self.current_file_index < len(self.files_list) - 1:
            self.load_file(self.current_file_index + 1)

    def load_previous_file(self):
        if self.current_file_index > 0:
            self.load_file(self.current_file_index - 1)

    def on_file_select(self, event):
        selected_indices = self.files_listbox.curselection()
        if selected_indices and selected_indices[0] != self.current_file_index:
            self.load_file(selected_indices[0])

    def _on_files_right_click(self, event):
        try:
            clicked_index = self.files_listbox.nearest(event.y)
            self.files_listbox.selection_clear(0, tk.END)
            self.files_listbox.selection_set(clicked_index)
            self.files_listbox.activate(clicked_index)
            context_menu = tk.Menu(self.root, tearoff=0)
            context_menu.add_command(label="Remove from Session", command=self.remove_selected_file_from_session)
            context_menu.tk_popup(event.x_root, event.y_root)
        except tk.TclError: pass

    def remove_selected_file_from_session(self):
        selected_indices = self.files_listbox.curselection()
        if not selected_indices: return
        index_to_delete = selected_indices[0]
        file_path_to_delete = self.files_list[index_to_delete]
        filename = os.path.basename(file_path_to_delete)

        if not messagebox.askyesno("Confirm Removal", f"Are you sure you want to remove '{filename}' from this session?", parent=self.root): return
        self.files_list.pop(index_to_delete)
        self.annotations.pop(file_path_to_delete, None)
        self.files_listbox.delete(index_to_delete)

        if self.current_file_index == index_to_delete:
            self.clear_views()
            self.current_file_path = None
            self.current_file_index = -1
            if self.files_list:
                new_index_to_load = min(index_to_delete, len(self.files_list) - 1)
                self.load_file(new_index_to_load)
            else:
                self.status_var.set("All files removed from session. Ready.")
                self.text_area.config(state=tk.DISABLED)
        elif self.current_file_index > index_to_delete:
            self.current_file_index -= 1

        self.status_var.set(f"Removed '{filename}' from the session.")
        self._update_button_states()
