# -*- coding: utf-8 -*-
import tkinter as tk
from bisect import bisect_left, bisect_right

class CoreMixin:
    """Pure, widget-free helpers shared across sections."""

    def _normalize_and_remap(self, text, spans):
        """
        Normalizes the text (all whitespace -> single space),
        and recalculates annotation offsets to match the normalized text.
        Also compensates for index misalignment caused by leading/trailing spaces.
        """
        mapping = {}
        new_text = []
        new_pos = 0
        i = 0

        while i < len(text):
            if text[i].isspace():
                mapping[i] = new_pos
                j = i + 1
                while j < len(text) and text[j].isspace():
                    mapping[j] = new_pos
                    j += 1
                new_text.append(' ')
                new_pos += 1
                i = j
            else:
                mapping[i] = new_pos
                new_text.append(text[i])
                new_pos += 1
                i += 1

        mapping[len(text)] = new_pos
        raw_normalized = ''.join(new_text)

        # Calculate how much the text shifts due to left strip()
        lstrip_len = len(raw_normalized) - len(raw_normalized.lstrip())
        normalized = raw_normalized.strip()

        remapped = []
        for span in spans:
            new_start = mapping.get(span["start"])
            new_end = mapping.get(span["end"])

            if new_start is not None and new_end is not None:
                    # Compensate for offset caused by strip()
                new_start -= lstrip_len
                new_end -= lstrip_len

                # Ensure span boundaries remain within string bounds
                new_start = max(0, new_start)
                new_end = min(len(normalized), new_end)

                if new_start < new_end:
                    remapped.append({
                        "start": new_start,
                        "end": new_end,
                        "label": span["label"]  # Either span["tag"] or span["label"], depending on what the method received
                    })

        return normalized, remapped

    def _sync_flat_tags(self):
        """Synchronizes the flat entity_tags list with the current hierarchy."""
        self.entity_tags = [tag for tags in self.tag_hierarchy.values() for tag in tags]

    def get_active_tags(self):
        """Returns a flat list of currently ACTIVE tags in hierarchical order."""
        active = []
        for layer, tags in self.tag_hierarchy.items():
            for tag in tags:
                if self.tag_active_states.get(tag, True):
                    active.append(tag)
        return active

    def _ensure_default_colors(self):
        for tag in self.entity_tags:
            self.get_color_for_tag(tag)

    def get_color_for_tag(self, tag):
        if tag not in self.tag_colors:
            try:
                if tag in self.entity_tags: self.tag_colors[tag] = next(self.color_cycle)
                else: return "#cccccc"
            except Exception: self.tag_colors[tag] = "#cccccc"
        return self.tag_colors.get(tag, "#cccccc")

    def _reset_state(self):
        self.clear_views()
        self.current_file_path = None
        self.files_list = []
        self.files_listbox.delete(0, tk.END)
        self.current_file_index = -1
        self.annotations = {}
        self.session_save_path = None
        self.root.title("ANNIE - Annotation Interface")
        self.status_var.set("Ready. Open a directory or load a session.")
        self.text_area.config(state=tk.DISABLED)
        self.last_used_ai_models = []
        self.current_ai_models = []

    def _build_entity_lookup_map(self, entities):
        self._entity_lookup_map.clear()
        for entity in entities:
            key = (entity['id'], entity['start_line'], entity['start_char'],
                   entity['end_line'], entity['end_char'], entity['tag'])
            self._entity_lookup_map[key] = entity

    def _tkinter_index_to_char_offset(self, text, line, char):
        lines = text.split('\n')
        offset = sum(len(l) + 1 for l in lines[:line - 1])
        offset += char
        return offset

    def _char_offset_to_tkinter_index(self, text, offset):
        if not self.line_start_offsets or offset < 0 or offset >= self.line_start_offsets[-1]:
            line_start = text.rfind('\n', 0, offset) + 1
            line = text.count('\n', 0, offset) + 1
            char = offset - line_start
            return f"{line}.{char}"

        line_idx = bisect_right(self.line_start_offsets, offset) - 1
        line = line_idx + 1
        char = offset - self.line_start_offsets[line_idx]
        return f"{line}.{char}"

    def _char_offset_to_tkinter_index_from_offsets(self, line_offsets, offset):
        line_idx = bisect_right(line_offsets, offset) - 1
        line = line_idx + 1
        char = offset - line_offsets[line_idx]
        return f"{line}.{char}"

    def _spans_overlap_numeric(self, start1_l, start1_c, end1_l, end1_c, start2_l, start2_c, end2_l, end2_c):
        span1_start, span1_end = (start1_l, start1_c), (end1_l, end1_c)
        span2_start, span2_end = (start2_l, start2_c), (end2_l, end2_c)
        return not ((span1_end <= span2_start) or (span1_start >= span2_end))

    def _is_overlapping_in_list(self, start_l, start_c, end_l, end_c, entities_list):
        for ann in entities_list:
            if self._spans_overlap_numeric(start_l, start_c, end_l, end_c, ann['start_line'], ann['start_char'], ann['end_line'], ann['end_char']): return True
        return False

    def _add_to_entity_lookup_map(self, entity):
        key = (entity['id'], entity['start_line'], entity['start_char'],
               entity['end_line'], entity['end_char'], entity['tag'])
        self._entity_lookup_map[key] = entity
