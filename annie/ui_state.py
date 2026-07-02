# -*- coding: utf-8 -*-
import tkinter as tk

class UIStateMixin:
    """Cross-cutting widget repaint + state-sync (the 'repaint quintet')."""

    def _configure_text_tags(self):
        for tag in self.entity_tags:
            color = self.get_color_for_tag(tag)
            try: self.text_area.tag_configure(tag, background=color, underline=False)
            except tk.TclError as e: print(f"Warning: Could not configure text tag '{tag}': {e}")
        try:
            if "propagated_entity" not in self.text_area.tag_names():
                self.text_area.tag_configure("propagated_entity", underline=True)

            if "low_confidence" not in self.text_area.tag_names():
                self.text_area.tag_configure("low_confidence", borderwidth=2, relief=tk.SOLID)

        except tk.TclError as e: print(f"Warning: Could not configure text tag: {e}")
        self.text_area.tag_configure("selection_highlight", borderwidth=2, relief=tk.SOLID)

    def _configure_treeview_tags(self):
        try: self.entities_tree.tag_configure('merged', foreground='grey', font=('TkDefaultFont', 9, 'italic'))
        except tk.TclError as e: print(f"Warning: Could not configure Treeview tags: {e}")

    def _update_entity_tag_combobox(self):
        current_selection = self.selected_entity_tag.get()
        active_tags = self.get_active_tags()

        if not active_tags:
            self.selected_entity_tag.set("")
            self.entity_tag_combobox.config(values=[], state=tk.DISABLED)
        else:
            sorted_tags = sorted(active_tags, key=str.lower)
            self.entity_tag_combobox['values'] = sorted_tags

            if current_selection not in active_tags:
                self.selected_entity_tag.set(sorted_tags[0])

            self.entity_tag_combobox.config(state="readonly")

    def _update_relation_type_combobox(self):
        current_selection = self.selected_relation_type.get()
        if not self.relation_types:
            self.selected_relation_type.set("")
            self.relation_type_combobox.config(values=[], state=tk.DISABLED)
        else:
            self.relation_type_combobox['values'] = self.relation_types
            if current_selection not in self.relation_types:
                self.selected_relation_type.set(self.relation_types[0])
            self.relation_type_combobox.config(state="readonly")

    def _update_button_states(self):
        file_loaded = bool(self.current_file_path)
        has_files = bool(self.files_list)
        num_entities_selected_rows = len(self.entities_tree.selection())
        num_relations_selected = len(self.relations_tree.selection())
        self.prev_btn.config(state=tk.NORMAL if has_files and self.current_file_index > 0 else tk.DISABLED)
        self.next_btn.config(state=tk.NORMAL if has_files and self.current_file_index < len(self.files_list) - 1 else tk.DISABLED)
        self.annotate_btn.config(state=tk.NORMAL if file_loaded and self.get_active_tags() else tk.DISABLED)
        self.remove_entity_btn.config(state=tk.NORMAL if num_entities_selected_rows > 0 else tk.DISABLED)
        self.merge_entities_btn.config(state=tk.NORMAL if num_entities_selected_rows >= 2 else tk.DISABLED)
        can_propagate_current = file_loaded and self.annotations.get(self.current_file_path, {}).get("entities")
        self.propagate_btn.config(state=tk.NORMAL if can_propagate_current else tk.DISABLED)
        can_add_relation = len(self.selected_entity_ids_for_relation) == 2 and self.relation_types
        self.add_relation_btn.config(state=tk.NORMAL if can_add_relation else tk.DISABLED)
        can_modify_relation = num_relations_selected == 1
        self.flip_relation_btn.config(state=tk.NORMAL if can_modify_relation else tk.DISABLED)
        self.remove_relation_btn.config(state=tk.NORMAL if can_modify_relation else tk.DISABLED)

    def clear_views(self):
        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL)
        try:
            self.text_area.delete(1.0, tk.END)
            tags_to_clear = set(self.entity_tags) | {"propagated_entity", "selection_highlight", "low_confidence", tk.SEL}
            for tag in tags_to_clear:
                try: self.text_area.tag_remove(tag, "1.0", tk.END)
                except tk.TclError: pass
        finally:
            self.text_area.config(state=original_state)
        try: self.entities_tree.delete(*self.entities_tree.get_children())
        except Exception: pass
        try: self.relations_tree.delete(*self.relations_tree.get_children())
        except Exception: pass
        self.selected_entity_ids_for_relation = []
        self._entity_id_to_tree_iids = {}
        self._entity_lookup_map.clear()
        self.line_start_offsets = [0]

    def apply_annotations_to_text(self):
        if not self.current_file_path: return
        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL)
        try:
            tags_to_clear = set(self.entity_tags) | {"propagated_entity", "low_confidence"}
            for tag in tags_to_clear: self.text_area.tag_remove(tag, "1.0", tk.END)

            entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
            for ann in entities:
                try:
                    start_pos = f"{ann['start_line']}.{ann['start_char']}"
                    end_pos = f"{ann['end_line']}.{ann['end_char']}"
                    tag = ann['tag']
                    if tag in self.entity_tags:
                        self.text_area.tag_add(tag, start_pos, end_pos)

                        if ann.get('score', 1.0) < 0.60:
                            self.text_area.tag_add("low_confidence", start_pos, end_pos)
                        elif ann.get('propagated'):
                            self.text_area.tag_add("propagated_entity", start_pos, end_pos)
                except Exception: pass
        finally:
            if self.text_area.winfo_exists(): self.text_area.config(state=original_state)

    def update_entities_list(self, selection_hint=None):
        try: self.entities_tree.delete(*self.entities_tree.get_children())
        except Exception: pass
        self._entity_id_to_tree_iids.clear()
        if not self.current_file_path: return

        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        if not entities:
            self.on_entity_select(None)
            return

        sorted_entities = sorted(entities, key=lambda a: (a['start_line'], a['start_char']))
        entity_id_counts = {eid: sum(1 for e in entities if e['id'] == eid) for eid in {e['id'] for e in entities}}

        for ann_index, ann in enumerate(sorted_entities):
            entity_id = ann.get('id', '')
            start_pos_str = f"{ann.get('start_line', 0)}.{ann.get('start_char', 0)}"
            end_pos_str = f"{ann.get('end_line', 0)}.{ann.get('end_char', 0)}"
            tag = ann.get('tag', 'N/A')
            full_text = ann.get('text', '')
            disp_text = full_text.replace('\n',' ').replace('\r', '')[:60]
            if len(full_text) > 60: disp_text += "..."

            tree_tags_tuple = ('merged',) if entity_id_counts.get(entity_id, 0) > 1 else ()
            tree_row_iid = f"entity|{entity_id}|{start_pos_str}|{end_pos_str}|{tag}|{ann_index}"
            values_tuple = (entity_id, start_pos_str, end_pos_str, disp_text, tag)
            self.entities_tree.insert("", tk.END, iid=tree_row_iid, values=values_tuple, tags=tree_tags_tuple)
            self._entity_id_to_tree_iids.setdefault(entity_id, []).append(tree_row_iid)

        new_iids_to_select = []
        all_iids_after = self.entities_tree.get_children()

        if isinstance(selection_hint, int) and all_iids_after:
            new_index = min(selection_hint, len(all_iids_after) - 1)
            new_iids_to_select.append(all_iids_after[new_index])
        elif isinstance(selection_hint, set):
            for iid in all_iids_after:
                try:
                    parts = iid.split('|')
                    key = (parts[1], parts[2], parts[3], parts[4])
                    if key in selection_hint: new_iids_to_select.append(iid)
                except IndexError: continue

        if new_iids_to_select: self.entities_tree.selection_set(new_iids_to_select)

        def restore_focus():
            current_selection = self.entities_tree.selection()
            if current_selection:
                self.entities_tree.focus(current_selection[0])
                self.entities_tree.see(current_selection[0])
                self.entities_tree.focus_set()
                self.on_entity_select(None)
        self.root.after(20, restore_focus)
        self._update_button_states()

    def update_relations_list(self):
        selected_iids = self.relations_tree.selection()
        try: self.relations_tree.delete(*self.relations_tree.get_children())
        except Exception: pass
        if not self.current_file_path: return
        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        relations = self.annotations.get(self.current_file_path, {}).get("relations", [])
        entity_display_map = { e['id']: e['text'][:25] + ('...' if len(e['text']) > 25 else '') for e in entities }
        for rel in sorted(relations, key=lambda r: r['type']):
            head_text = entity_display_map.get(rel['head_id'], f"ID: {rel['head_id'][:6]}...")
            tail_text = entity_display_map.get(rel['tail_id'], f"ID: {rel['tail_id'][:6]}...")
            values = (rel['id'], head_text, rel['type'], tail_text)
            self.relations_tree.insert("", tk.END, iid=rel['id'], values=values)
        if selected_iids: self.relations_tree.selection_set(selected_iids)
        self._update_button_states()
