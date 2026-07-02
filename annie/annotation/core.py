# -*- coding: utf-8 -*-
import tkinter as tk
from tkinter import messagebox
import uuid
import traceback
import os

class AnnotationMixin:
    """Entity/relation annotation logic (sink)."""

    def annotate_selection(self):
        if not self.current_file_path or not self.get_active_tags(): return
        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL)
        try:
            try:
                start_pos = self.text_area.index(tk.SEL_FIRST)
                end_pos = self.text_area.index(tk.SEL_LAST)
            except tk.TclError: return
            if start_pos == end_pos: return

            if self.selection_mode.get() == "word":
                calc_start_pos = self.text_area.index(f"{start_pos} wordstart")
                calc_end_pos = self.text_area.index(f"{self.text_area.index(f'{end_pos}-1c')} wordend")
            else:
                calc_start_pos = start_pos
                calc_end_pos = end_pos

            if self.text_area.compare(calc_start_pos, ">=", calc_end_pos): return
            raw_text = self.text_area.get(calc_start_pos, calc_end_pos)

            leading_spaces = len(raw_text) - len(raw_text.lstrip())
            trailing_spaces = len(raw_text) - len(raw_text.rstrip())
            final_text = raw_text.strip()
            if not final_text: return

            final_start_pos = self.text_area.index(f"{calc_start_pos}+{leading_spaces}c")
            final_end_pos = self.text_area.index(f"{calc_end_pos}-{trailing_spaces}c")
            start_line, start_char = map(int, final_start_pos.split('.'))
            end_line, end_char = map(int, final_end_pos.split('.'))

            tag = self.selected_entity_tag.get()
            if not tag: return

            entities_in_file = self.annotations.get(self.current_file_path, {}).get("entities", [])
            if not self.allow_multilabel_overlap.get():
                if self._is_overlapping_in_list(start_line, start_char, end_line, end_char, entities_in_file):
                    messagebox.showwarning("Overlap Detected", "Annotation overlaps with an existing one.", parent=self.root)
                    return
            else:
                for ann in entities_in_file:
                    if (ann['start_line'] == start_line and ann['start_char'] == start_char and
                        ann['end_line'] == end_line and ann['end_char'] == end_char and ann['tag'] == tag):
                        self.status_var.set("This exact annotation already exists.")
                        return

            entity_id = uuid.uuid4().hex
            annotation = {'id': entity_id, 'start_line': start_line, 'start_char': start_char,
                          'end_line': end_line, 'end_char': end_char, 'text': final_text, 'tag': tag}
            entities_in_file.append(annotation)
            self._add_to_entity_lookup_map(annotation)

            self.text_area.tag_remove(tk.SEL, "1.0", tk.END)
            self.apply_annotations_to_text()
            self.update_entities_list()
            self.status_var.set(f"Annotated: '{final_text[:30].replace(os.linesep, ' ')}...' as {tag}")
            self._update_button_states()
        except Exception as e:
            traceback.print_exc()
        finally:
            if self.text_area.winfo_exists() and original_state == tk.DISABLED: self.text_area.config(state=tk.DISABLED)

    def _ask_confirm_deletion_with_option(self, title, message, checkbox_text):
        dialog = tk.Toplevel(self.root)
        dialog.title(title)
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.resizable(False, False)
        result = {"confirmed": False, "option": False}
        main_frame = tk.Frame(dialog, padx=20, pady=15)
        main_frame.pack(fill="both", expand=True)
        tk.Label(main_frame, text=message, wraplength=350, justify=tk.LEFT).pack(pady=(0, 20))
        option_var = tk.BooleanVar()
        tk.Checkbutton(main_frame, text=checkbox_text, variable=option_var).pack(anchor=tk.W, pady=(0, 15))
        btn_frame = tk.Frame(main_frame)
        btn_frame.pack(fill=tk.X)
        def on_ok():
            result["confirmed"] = True
            result["option"] = option_var.get()
            dialog.destroy()
        def on_cancel():
            result["confirmed"] = False
            dialog.destroy()
        cancel_btn = tk.Button(btn_frame, text="Cancel", width=10, command=on_cancel)
        cancel_btn.pack(side=tk.RIGHT, padx=(10, 0))
        ok_btn = tk.Button(btn_frame, text="Delete", width=10, command=on_ok, default=tk.ACTIVE)
        ok_btn.pack(side=tk.RIGHT)
        dialog.protocol("WM_DELETE_WINDOW", on_cancel)
        dialog.bind('<Return>', lambda event: ok_btn.invoke())
        dialog.bind('<Escape>', lambda event: cancel_btn.invoke())
        self.root.update_idletasks()
        x = self.root.winfo_x() + (self.root.winfo_width() - dialog.winfo_reqwidth()) / 2
        y = self.root.winfo_y() + (self.root.winfo_height() - dialog.winfo_reqheight()) / 2
        dialog.geometry(f"+{int(x)}+{int(y)}")
        ok_btn.focus_set()
        self.root.wait_window(dialog)
        return result

    def _remove_text_tag_from_corpus(self, text_to_delete, tag_to_delete):
        if not messagebox.askokcancel("Permanent Deletion",
                                      f"Are you sure you want to delete ALL occurrences of\n\n"
                                      f"Text: '{text_to_delete}'\nTag: '{tag_to_delete}'\n\nfrom the entire corpus?",
                                      icon='warning', parent=self.root): return
        self.status_var.set("Performing corpus-wide deletion...")
        self.progress_bar.start()
        self.root.update()
        removed_count = 0
        affected_files = set()
        normalized_text = text_to_delete.strip().lower()

        for file_path, data in self.annotations.items():
            entities = data.get("entities", [])
            if not entities: continue
            initial_count = len(entities)
            ids_to_check = set()
            entities_to_keep = []
            for entity in entities:
                if entity.get('text', '').strip().lower() == normalized_text and entity.get('tag') == tag_to_delete:
                    ids_to_check.add(entity['id'])
                    removed_count += 1
                else: entities_to_keep.append(entity)

            if len(entities_to_keep) < initial_count:
                affected_files.add(file_path)
                data["entities"] = entities_to_keep
                remaining_ids = {e['id'] for e in entities_to_keep}
                orphaned_ids = ids_to_check - remaining_ids
                if orphaned_ids and "relations" in data:
                    data["relations"] = [r for r in data["relations"] if r['head_id'] not in orphaned_ids and r['tail_id'] not in orphaned_ids]

        self.progress_bar.stop()
        if self.current_file_path in affected_files:
            self._build_entity_lookup_map(self.annotations.get(self.current_file_path, {}).get('entities', []))
            self.apply_annotations_to_text()
            self.update_entities_list()
            self.update_relations_list()
        self.status_var.set(f"Deleted {removed_count} annotations from {len(affected_files)} files.")

    def _handle_entity_deletion(self, entities_to_delete):
        if not entities_to_delete: return
        if self._is_deleting: return
        self._is_deleting = True
        try:
            first_entity = entities_to_delete[0]
            rep_text = first_entity.get('text', '')
            rep_tag = first_entity.get('tag', '')

            confirm_result = self._ask_confirm_deletion_with_option(
                title="Confirm Deletion",
                message=f"Are you sure you want to delete the selected {len(entities_to_delete)} annotation(s)?",
                checkbox_text=f"Delete all \"{rep_text[:20]}...\" ({rep_tag}) from the entire corpus"
            )
            if not confirm_result["confirmed"]:
                self.status_var.set("Deletion cancelled.")
                return
            if confirm_result["option"]:
                self._remove_text_tag_from_corpus(rep_text, rep_tag)
            else:
                all_iids_before = self.entities_tree.get_children()
                next_selection_index = 0
                if all_iids_before:
                    try:
                        first_id, first_sl, first_sc, first_el, first_ec, first_tag = (
                            first_entity['id'], first_entity['start_line'], first_entity['start_char'],
                            first_entity['end_line'], first_entity['end_char'], first_entity['tag'])
                        for i, iid in enumerate(all_iids_before):
                            parts = iid.split('|')
                            if (parts[1] == first_id and int(parts[2].split('.')[0]) == first_sl and int(parts[2].split('.')[1]) == first_sc and
                                int(parts[3].split('.')[0]) == first_el and int(parts[3].split('.')[1]) == first_ec and parts[4] == first_tag):
                                next_selection_index = i
                                break
                    except (ValueError, IndexError): pass

                entities_in_file = self.annotations.get(self.current_file_path, {}).get("entities", [])
                ids_to_remove = {e['id'] for e in entities_to_delete}
                for item in entities_to_delete:
                    if item in entities_in_file: entities_in_file.remove(item)
                    key = (item['id'], item['start_line'], item['start_char'], item['end_line'], item['end_char'], item['tag'])
                    self._entity_lookup_map.pop(key, None)

                relations = self.annotations[self.current_file_path].get("relations", [])
                if relations:
                    remaining_ids = {e['id'] for e in entities_in_file}
                    orphaned_ids = ids_to_remove - remaining_ids
                    if orphaned_ids:
                        self.annotations[self.current_file_path]["relations"] = [r for r in relations if r['head_id'] not in orphaned_ids and r['tail_id'] not in orphaned_ids]

                self.apply_annotations_to_text()
                self.update_relations_list()
                self.update_entities_list(selection_hint=next_selection_index)
                self.status_var.set(f"Removed {len(entities_to_delete)} entity instance(s).")
        finally:
            self._is_deleting = False

    def remove_entity_annotation(self, event=None):
        selected_iids = self.entities_tree.selection()
        if not selected_iids:
            messagebox.showinfo("Info", "Select one or more entities to remove.", parent=self.root)
            return
        entities_to_delete = []
        for iid in selected_iids:
            try:
                parts = iid.split('|')
                if len(parts) < 6: continue
                entity_key = (parts[1], int(parts[2].split('.')[0]), int(parts[2].split('.')[1]),
                              int(parts[3].split('.')[0]), int(parts[3].split('.')[1]), parts[4])
                entity_dict = self._entity_lookup_map.get(entity_key)
                if entity_dict: entities_to_delete.append(entity_dict)
            except (ValueError, IndexError): continue
        self._handle_entity_deletion(entities_to_delete)

    def merge_selected_entities(self):
        selected_tree_iids = self.entities_tree.selection()
        if len(selected_tree_iids) < 2: return
        selected_entities_data = []
        for tree_iid in selected_tree_iids:
            try:
                parts = tree_iid.split('|')
                if len(parts) < 6: continue
                entity_key = (parts[1], int(parts[2].split('.')[0]), int(parts[2].split('.')[1]),
                              int(parts[3].split('.')[0]), int(parts[3].split('.')[1]), parts[4])
                entity_dict = self._entity_lookup_map.get(entity_key)
                if entity_dict and entity_dict not in selected_entities_data:
                    selected_entities_data.append(entity_dict)
            except Exception: pass

        if len(selected_entities_data) < 2: return
        selected_entities_data.sort(key=lambda e: (e['start_line'], e['start_char']))
        canonical_entity = selected_entities_data[0]
        canonical_id = canonical_entity['id']
        ids_to_change = {e['id'] for e in selected_entities_data if e['id'] != canonical_id}

        if not ids_to_change: return
        for entity in selected_entities_data:
            if entity['id'] in ids_to_change:
                old_key = (entity['id'], entity['start_line'], entity['start_char'], entity['end_line'], entity['end_char'], entity['tag'])
                self._entity_lookup_map.pop(old_key, None)
                entity['id'] = canonical_id
                new_key = (entity['id'], entity['start_line'], entity['start_char'], entity['end_line'], entity['end_char'], entity['tag'])
                self._entity_lookup_map[new_key] = entity

        relations = self.annotations[self.current_file_path].get("relations", [])
        if relations:
            for rel in relations:
                if rel['head_id'] in ids_to_change: rel['head_id'] = canonical_id
                if rel['tail_id'] in ids_to_change: rel['tail_id'] = canonical_id
            unique_relations = { (r['head_id'], r['type'], r['tail_id']): r for r in relations }.values()
            self.annotations[self.current_file_path]['relations'] = list(unique_relations)

        self.update_entities_list()
        self.update_relations_list()
        self.apply_annotations_to_text()

    def _on_text_right_click(self, event):
        if not self.current_file_path: return
        try:
            click_index_str = self.text_area.index(f"@{event.x},{event.y}")
            click_pos = tuple(map(int, click_index_str.split('.')))
        except (tk.TclError, ValueError): return

        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        clicked_entity = None
        for entity in reversed(entities):
            start_pos_tuple = (entity['start_line'], entity['start_char'])
            end_pos_tuple = (entity['end_line'], entity['end_char'])
            if start_pos_tuple <= click_pos < end_pos_tuple:
                clicked_entity = entity
                break

        if not clicked_entity: return
        context_menu = tk.Menu(self.root, tearoff=0)
        entity_id = clicked_entity['id']
        count = sum(1 for e in entities if e['id'] == entity_id)

        if count > 1:
            context_menu.add_command(label="Demerge This Instance", command=lambda e=clicked_entity: self.demerge_entity(e))
            context_menu.add_separator()
        context_menu.add_command(label=f"ID: {entity_id[:8]}... ({'Merged' if count > 1 else 'Unique'})", state=tk.DISABLED)
        context_menu.tk_popup(event.x_root, event.y_root)

    def demerge_entity(self, entity_to_demerge):
        old_key = (entity_to_demerge['id'], entity_to_demerge['start_line'], entity_to_demerge['start_char'],
                   entity_to_demerge['end_line'], entity_to_demerge['end_char'], entity_to_demerge['tag'])
        self._entity_lookup_map.pop(old_key, None)
        entity_to_demerge['id'] = uuid.uuid4().hex
        self._add_to_entity_lookup_map(entity_to_demerge)
        self.update_entities_list()
        self.apply_annotations_to_text()

    def on_entity_select(self, event=None):
        selected_tree_iids = self.entities_tree.selection()
        unique_ids = set()
        for iid in selected_tree_iids:
            try: unique_ids.add(iid.split('|')[1])
            except IndexError: pass
        self.selected_entity_ids_for_relation = list(unique_ids)
        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL)
        try:
            self.text_area.tag_remove("selection_highlight", "1.0", tk.END)
            first_pos = None
            for iid in selected_tree_iids:
                try:
                    parts = iid.split('|')
                    start_pos, end_pos = parts[2], parts[3]
                    self.text_area.tag_add("selection_highlight", start_pos, end_pos)
                    if first_pos is None: first_pos = start_pos
                except (IndexError, tk.TclError): pass
            if first_pos: self.text_area.see(first_pos)
        finally:
            if self.text_area.winfo_exists(): self.text_area.config(state=original_state)
        self._update_button_states()

    def add_relation(self):
        if len(self.selected_entity_ids_for_relation) != 2: return
        head_id, tail_id = self.selected_entity_ids_for_relation
        relation_type = self.selected_relation_type.get()
        if not relation_type: return
        relations_list = self.annotations.setdefault(self.current_file_path, {}).setdefault("relations", [])
        if any(r['head_id'] == head_id and r['tail_id'] == tail_id and r['type'] == relation_type for r in relations_list): return
        new_relation = {"id": uuid.uuid4().hex, "type": relation_type, "head_id": head_id, "tail_id": tail_id}
        relations_list.append(new_relation)
        self.update_relations_list()

    def flip_selected_relation(self):
        selected_iids = self.relations_tree.selection()
        if not selected_iids: return
        relation_id = selected_iids[0]
        relations = self.annotations[self.current_file_path].get("relations", [])
        for rel in relations:
            if rel['id'] == relation_id:
                rel['head_id'], rel['tail_id'] = rel['tail_id'], rel['head_id']
                self.update_relations_list()
                break

    def remove_relation_annotation(self, event=None):
        selected_iids = self.relations_tree.selection()
        if not selected_iids: return
        relation_id = selected_iids[0]
        relations = self.annotations[self.current_file_path].get("relations", [])
        self.annotations[self.current_file_path]["relations"] = [r for r in relations if r['id'] != relation_id]
        self.update_relations_list()

    def on_relation_select(self, event=None):
        self._update_button_states()
