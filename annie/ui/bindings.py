# -*- coding: utf-8 -*-
import time

class BindingsMixin:
    """Mouse / hotkey dispatchers."""

    def _on_mouse_down(self, event):
        self._click_time = time.time()
        self._click_pos = (event.x, event.y)

    def _on_hotkey_press(self, event):
        try:
            key_num = int(event.keysym)
            tag_index = (key_num - 1) % 10 if key_num != 0 else 9
            active_tags = self.get_active_tags()
            if not (0 <= tag_index < len(active_tags)): return
            new_tag = active_tags[tag_index]
            selected_iids = self.entities_tree.selection()

            if selected_iids:
                if not self.current_file_path: return
                entities_to_relabel = []
                for iid in selected_iids:
                    try:
                        parts = iid.split('|')
                        if len(parts) < 6: continue
                        entity_key = (parts[1], int(parts[2].split('.')[0]), int(parts[2].split('.')[1]),
                                      int(parts[3].split('.')[0]), int(parts[3].split('.')[1]), parts[4])
                        entity = self._entity_lookup_map.get(entity_key)
                        if entity: entities_to_relabel.append(entity)
                    except (ValueError, IndexError): continue

                if not entities_to_relabel:
                    self.status_var.set("No valid entities selected for relabeling.")
                    return

                for entity_dict in entities_to_relabel:
                    old_key = (entity_dict['id'], entity_dict['start_line'], entity_dict['start_char'],
                               entity_dict['end_line'], entity_dict['end_char'], entity_dict['tag'])
                    self._entity_lookup_map.pop(old_key, None)
                    entity_dict['tag'] = new_tag
                    new_key = (entity_dict['id'], entity_dict['start_line'], entity_dict['start_char'],
                               entity_dict['end_line'], entity_dict['end_char'], new_tag)
                    self._entity_lookup_map[new_key] = entity_dict

                self.apply_annotations_to_text()
                selection_info_for_rebuild = {(e['id'], f"{e['start_line']}.{e['start_char']}",
                                               f"{e['end_line']}.{e['end_char']}", new_tag) for e in entities_to_relabel}
                self.update_entities_list(selection_hint=selection_info_for_rebuild)
                self.status_var.set(f"Relabeled {len(entities_to_relabel)} entit{'y' if len(entities_to_relabel) == 1 else 'ies'} to '{new_tag}'")
            else:
                self.selected_entity_tag.set(new_tag)
                self.status_var.set(f"Selected Tag: {new_tag}")
            return "break"
        except (ValueError, IndexError): pass
