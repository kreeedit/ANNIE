# -*- coding: utf-8 -*-
"""
ANNIE: Annotation Interface for Named-entity & Information Extraction.
Includes Hierarchical Tagging, Hybrid Ensemble AI (Session Memory + HF Models),
Sentence-level conversion, and Global Search.
"""

import os
import shutil
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import json
from pathlib import Path
import uuid
import itertools
import re
import traceback
import time
import threading
import torch
import queue
from bisect import bisect_left, bisect_right
import requests
import math
from collections import Counter

# --- Constants ---
SESSION_FILE_VERSION = "1.14"


class TextAnnotator:
    """Handles UI creation, file loading, annotation logic, and saving."""
    def __init__(self, root_window):
        self.root = root_window
        self.root.title("ANNIE - Annotation Interface")
        self.root.geometry("1200x850")

        # --- Core Data ---
        self.current_file_path = None
        self.files_list = []
        self.current_file_index = -1
        self.annotations = {}
        self.session_save_path = None

        # --- Optimized Data Structures ---
        self.line_start_offsets = [0]
        self._entity_lookup_map = {}

        # --- Entity Tagging Configuration (Hierarchical) ---
        self.tag_hierarchy = {
            "CORE Layer": ["PER", "LOC", "INS", "DAT", "TIM"],
            "ANALYTICAL Layer": ["TITLE", "REL", "TAX", "MEA", "COM", "EST", "MON", "NUM", "LEG", "NAT"],
            "SPAN Layer": ["ACTOR", "PROP", "TRANS"]
        }
        self.tag_active_states = {tag: True for layer in self.tag_hierarchy.values() for tag in layer}
        self.tag_propagation_states = {tag: True for layer in self.tag_hierarchy.values() for tag in layer}

        self.entity_tags = []
        self._sync_flat_tags()
        self.selected_entity_tag = tk.StringVar(value=self.get_active_tags()[0] if self.get_active_tags() else "")
        self.extend_to_word = tk.BooleanVar(value=False)
        self.allow_multilabel_overlap = tk.BooleanVar(value=True)

        # --- Relation Tagging Configuration ---
        self.relation_types = ["spouse_of", "works_at", "located_in", "born_on", "produces"]
        self.selected_relation_type = tk.StringVar(value=self.relation_types[0] if self.relation_types else "")
        self.selection_mode = tk.StringVar(value="word")

        # --- UI State ---
        self.selected_entity_ids_for_relation = []
        self._entity_id_to_tree_iids = {}
        self._click_time = 0
        self._click_pos = (0, 0)
        self._is_deleting = False
        self._is_annotating_ai = False
        self._just_double_clicked = False
        self.last_used_ai_models = []
        self.current_ai_models = []

        # --- AI Settings State ---
        self.ai_min_conf = 0.90
        self.ai_max_conf = 1.00
        self.ai_label_mapping = {}

        self.llm_provider = "Anthropic (Claude)"
        # --- LLM Agent State ---
        self.llm_models = {
            "OpenAI": "gpt-4o-mini",
            "Anthropic (Claude)": "claude-sonnet-4-6",
            "Together AI": "meta-llama/Meta-Llama-3.1-8B-Instruct-Turbo",
            "Hugging Face": "HuggingFaceH4/zephyr-7b-alpha"
        }
        self.llm_model = self.llm_models[self.llm_provider]

        self._load_api_keys()
        self.llm_few_shot_count = 3

        # --- Sort Tracking ---
        self.entities_sort_column = None
        self.entities_sort_reverse = False
        self.relations_sort_column = None
        self.relations_sort_reverse = False

        # --- Colors ---
        self.tag_colors = {
            "PER": "#ffcccc", "LOC": "#ccccff", "INS": "#ccffcc",
            "DAT": "#ffffcc", "TITLE": "#ccffff"
        }
        self.color_cycle = itertools.cycle([
            "#e6e6fa", "#ffe4e1", "#f0fff0", "#fffacd", "#add8e6",
            "#f5f5dc", "#d3ffd3", "#fafad2", "#ffebcd", "#e0ffff"
        ])
        self._ensure_default_colors()

        # --- Status Bar and Progress Bar Setup ---
        self.status_var = tk.StringVar(value="Ready. Open a directory or load a session.")
        status_frame = tk.Frame(self.root, bd=1, relief=tk.SUNKEN)
        status_frame.pack(side=tk.BOTTOM, fill=tk.X)
        status_inner_frame = tk.Frame(status_frame, height=25)
        status_inner_frame.pack(fill=tk.X, expand=True)
        status_inner_frame.pack_propagate(False)
        status_label = tk.Label(status_inner_frame, textvariable=self.status_var, anchor=tk.W, background='gray85')
        status_label.pack(side=tk.LEFT, padx=5, pady=2, fill=tk.X, expand=True)
        self.progress_bar = ttk.Progressbar(status_inner_frame, orient='horizontal', mode='indeterminate', length=200)
        self.progress_bar.pack(side=tk.RIGHT, padx=5, pady=2, fill=tk.X, expand=False)
        self.progress_bar.stop()
        self.ai_status_queue = queue.Queue()
        self._process_queue()

        # --- Build UI ---
        self.create_menu()
        self.create_layout()

        # --- Initial UI Setup ---
        self._update_entity_tag_combobox()
        self._update_relation_type_combobox()
        self._configure_text_tags()
        self._configure_treeview_tags()
        self._update_button_states()

        # --- Bind Hotkeys ---
        for i in range(10):
            self.root.bind(str(i), self._on_hotkey_press)
        # AI
        self.root.bind('a', lambda event: self.run_ai_annotation_from_hotkey())
        # Generative
        self.root.bind('g', lambda event: self.run_llm_agent_from_hotkey())
        self.root.protocol("WM_DELETE_WINDOW", self._on_closing)
        self.root.bind('<Control-f>', self.find_text_dialog)


    def _normalize_and_remap(self, text, spans):
        """
        Normalizálja a szöveget (minden whitespace -> egy szóköz),
        és újraszámolja az annotációs offseteket a normalizált szövegre.
        A vezető/záró szóközök okozta index-elcsúszást is kompenzálja.
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

        # Kiszámoljuk, mennyit tolódik a szöveg a baloldali strip() miatt
        lstrip_len = len(raw_normalized) - len(raw_normalized.lstrip())
        normalized = raw_normalized.strip()

        remapped = []
        for span in spans:
            new_start = mapping.get(span["start"])
            new_end = mapping.get(span["end"])

            if new_start is not None and new_end is not None:
                # Kompenzáljuk a strip() miatti elcsúszást
                new_start -= lstrip_len
                new_end -= lstrip_len

                # Biztosítjuk, hogy a span határok a stringen belül maradjanak
                new_start = max(0, new_start)
                new_end = min(len(normalized), new_end)

                if new_start < new_end:
                    remapped.append({
                        "start": new_start,
                        "end": new_end,
                        "label": span["label"] # Vagy span["tag"], attól függően, mit kapott a metódus
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

    def create_menu(self):
        menubar = tk.Menu(self.root)
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Open Directory", command=self.load_directory)
        file_menu.add_command(label="Add File(s) to Session...", command=self.add_files_to_session)
        file_menu.add_command(label="Convert Session to Sentence Mode...", command=self.convert_session_to_sentences)
        file_menu.add_separator()
        file_menu.add_command(label="Load Session...", command=self.load_session)
        file_menu.add_command(label="Save Session", command=self.save_session)
        file_menu.add_command(label="Save Session As...", command=lambda: self.save_session(force_ask=True))
        file_menu.add_separator()
        file_menu.add_command(label="Import Annotations...", command=self.import_annotations)
        file_menu.add_command(label="Export for Training...", command=self.export_annotations)
        file_menu.add_separator()
        file_menu.add_command(label="Save Annotations Only...", command=self.save_annotations)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self._on_closing)
        menubar.add_cascade(label="File", menu=file_menu)

        self.settings_menu = tk.Menu(menubar, tearoff=0)
        self.settings_menu.add_command(label="Manage Entity Tags...", command=self.manage_entity_tags)
        self.settings_menu.add_command(label="Manage Relation Types...", command=self.manage_relation_types)
        self.settings_menu.add_separator()
        self.settings_menu.add_command(label="Load Tag/Relation Schema...", command=self.load_schema)
        self.settings_menu.add_command(label="Save Tag/Relation Schema...", command=self.save_schema)
        self.settings_menu.add_separator()
        self.settings_menu.add_command(label="Load Dictionary & Propagate Entities...", command=self.load_and_propagate_from_dictionary)
        self.settings_menu.add_command(label="Pre-annotate with Hybrid AI...", command=self.pre_annotate_with_ai)
        self.settings_menu.add_command(label="Predict Current from Session Memory...", command=self.predict_from_session_memory)
        self.settings_menu.add_command(label="Generative LLM Agent (Few-Shot)...", command=self.show_llm_settings_dialog)
        self.settings_menu.add_separator()
        mode_menu = tk.Menu(self.settings_menu, tearoff=0)
        self.settings_menu.add_cascade(label="Selection Mode (Session Type)", menu=mode_menu)
        mode_menu.add_radiobutton(label="Word-based (Snap to whole words)", variable=self.selection_mode, value="word")
        mode_menu.add_radiobutton(label="Character-based (Exact selection)", variable=self.selection_mode, value="char")
        self.settings_menu.add_checkbutton(label="Allow Multi-label & Overlapping Annotations", variable=self.allow_multilabel_overlap, onvalue=True, offvalue=False)
        menubar.add_cascade(label="Settings", menu=self.settings_menu)
        self.root.config(menu=menubar)

    def create_layout(self):
        main_frame = tk.Frame(self.root)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        left_frame = tk.Frame(main_frame, width=200)
        left_frame.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 10))
        left_frame.pack_propagate(False)
        tk.Label(left_frame, text="Files:").pack(anchor=tk.W)
        files_frame = tk.Frame(left_frame)
        files_frame.pack(fill=tk.BOTH, expand=True)
        scrollbar_files = tk.Scrollbar(files_frame)
        scrollbar_files.pack(side=tk.RIGHT, fill=tk.Y)
        self.files_listbox = tk.Listbox(files_frame, yscrollcommand=scrollbar_files.set, exportselection=False)
        self.files_listbox.pack(fill=tk.BOTH, expand=True)
        self.files_listbox.bind('<<ListboxSelect>>', self.on_file_select)
        self.files_listbox.bind('<Button-3>', self._on_files_right_click)
        self.files_listbox.bind('<Button-2>', self._on_files_right_click)
        scrollbar_files.config(command=self.files_listbox.yview)
        nav_frame = tk.Frame(left_frame)
        nav_frame.pack(fill=tk.X, pady=5)
        self.prev_btn = tk.Button(nav_frame, text="Previous", command=self.load_previous_file, state=tk.DISABLED)
        self.prev_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 2))
        self.next_btn = tk.Button(nav_frame, text="Next", command=self.load_next_file, state=tk.DISABLED)
        self.next_btn.pack(side=tk.RIGHT, fill=tk.X, expand=True, padx=(2, 0))

        right_frame = tk.Frame(main_frame)
        right_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
        right_main_pane = tk.PanedWindow(right_frame, orient=tk.VERTICAL, sashrelief=tk.RAISED, sashwidth=6)
        right_main_pane.pack(fill=tk.BOTH, expand=True)
        text_outer_frame = tk.Frame(right_main_pane)
        right_main_pane.add(text_outer_frame, stretch="always", minsize=150)
        text_frame = tk.Frame(text_outer_frame)
        text_frame.pack(fill=tk.BOTH, expand=True)
        scrollbar_text_y = tk.Scrollbar(text_frame)
        scrollbar_text_y.pack(side=tk.RIGHT, fill=tk.Y)
        scrollbar_text_x = tk.Scrollbar(text_frame, orient=tk.HORIZONTAL)
        scrollbar_text_x.pack(side=tk.BOTTOM, fill=tk.X)
        self.text_area = tk.Text(text_frame, wrap=tk.WORD, yscrollcommand=scrollbar_text_y.set,
                                 xscrollcommand=scrollbar_text_x.set, undo=True, state=tk.DISABLED,
                                 borderwidth=1, relief="sunken", insertbackground="black", insertwidth=2,
                                 takefocus=False)
        self.text_area.pack(fill=tk.BOTH, expand=True)
        scrollbar_text_y.config(command=self.text_area.yview)
        scrollbar_text_x.config(command=self.text_area.xview)
        self.text_area.bind("<ButtonPress-1>", self._on_mouse_down)
        self.text_area.bind("<ButtonRelease-1>", self._on_highlight_release)
        self.text_area.bind("<Double-Button-1>", self._on_double_click)
        self.text_area.bind("<Button-3>", self._on_text_right_click)
        self.text_area.bind("<Button-2>", self._on_text_right_click)

        controls_panel = tk.Frame(right_main_pane, bd=1, relief=tk.SUNKEN)
        right_main_pane.add(controls_panel, stretch="never")
        entity_controls_frame = tk.LabelFrame(controls_panel, text="Entity Annotation", padx=5, pady=5)
        entity_controls_frame.pack(side=tk.LEFT, padx=(5, 5), pady=5, fill=tk.X, expand=True)
        ecf_top = tk.Frame(entity_controls_frame)
        ecf_top.grid(row=0, column=0, sticky="ew", pady=(0, 5))
        tk.Label(ecf_top, text="Tag:").pack(side=tk.LEFT)
        self.entity_tag_combobox = ttk.Combobox(ecf_top, textvariable=self.selected_entity_tag, values=self.entity_tags, width=12, state="readonly")
        self.entity_tag_combobox.pack(side=tk.LEFT, padx=5)
        self.annotate_btn = tk.Button(ecf_top, text="Annotate Sel", command=self.annotate_selection, state=tk.DISABLED, width=10)
        self.annotate_btn.pack(side=tk.LEFT, padx=5)
        self.remove_entity_btn = tk.Button(ecf_top, text="Remove Sel", command=self.remove_entity_annotation, state=tk.DISABLED, width=10)
        self.remove_entity_btn.pack(side=tk.LEFT, padx=5)
        self.merge_entities_btn = tk.Button(ecf_top, text="Merge Sel.", command=self.merge_selected_entities, state=tk.DISABLED, width=10)
        self.merge_entities_btn.pack(side=tk.LEFT, padx=5)

        ecf_bottom = tk.Frame(entity_controls_frame)
        ecf_bottom.grid(row=1, column=0, sticky="ew")
        self.extend_checkbox = tk.Checkbutton(ecf_bottom, text="Extend to word", variable=self.extend_to_word)
        self.extend_checkbox.pack(side=tk.LEFT, anchor=tk.W)
        self.propagate_btn = tk.Button(ecf_bottom, text="Propagate Entities", command=self.propagate_annotations, state=tk.DISABLED)
        self.propagate_btn.pack(side=tk.LEFT, padx=10)

        relation_controls_frame = tk.LabelFrame(controls_panel, text="Relation Annotation", padx=5, pady=5)
        relation_controls_frame.pack(side=tk.LEFT, padx=(0, 5), pady=5, fill=tk.X, expand=True)
        tk.Label(relation_controls_frame, text="Type:").pack(side=tk.LEFT)
        self.relation_type_combobox = ttk.Combobox(relation_controls_frame, textvariable=self.selected_relation_type, values=self.relation_types, width=12, state="readonly")
        self.relation_type_combobox.pack(side=tk.LEFT, padx=5)
        self.add_relation_btn = tk.Button(relation_controls_frame, text="Add Relation (Head->Tail)", command=self.add_relation, state=tk.DISABLED, width=20)
        self.add_relation_btn.pack(side=tk.LEFT, padx=(5, 2))
        self.flip_relation_btn = tk.Button(relation_controls_frame, text="Flip H/T", command=self.flip_selected_relation, state=tk.DISABLED, width=7)
        self.flip_relation_btn.pack(side=tk.LEFT, padx=2)
        self.remove_relation_btn = tk.Button(relation_controls_frame, text="Remove Relation", command=self.remove_relation_annotation, state=tk.DISABLED, width=14)
        self.remove_relation_btn.pack(side=tk.LEFT, padx=(2, 5))

        list_outer_frame = tk.Frame(right_main_pane)
        right_main_pane.add(list_outer_frame, stretch="always", minsize=150)
        list_panel = tk.PanedWindow(list_outer_frame, orient=tk.VERTICAL, sashrelief=tk.RAISED, sashwidth=4)
        list_panel.pack(fill=tk.BOTH, expand=True)

        entities_list_frame = tk.LabelFrame(list_panel, text="Entities", padx=5, pady=5)
        list_panel.add(entities_list_frame, stretch="always", minsize=75)
        entities_tree_frame = tk.Frame(entities_list_frame)
        entities_tree_frame.pack(fill=tk.BOTH, expand=True)
        scrollbar_entities_y = tk.Scrollbar(entities_tree_frame)
        scrollbar_entities_y.pack(side=tk.RIGHT, fill=tk.Y)
        self.entities_tree = ttk.Treeview(entities_tree_frame, columns=("ID", "Start", "End", "Text", "Tag"),
                                          displaycolumns=("Start", "End", "Text", "Tag"), show="headings",
                                          yscrollcommand=scrollbar_entities_y.set, selectmode='extended')
        self.entities_tree.column("ID", width=0, stretch=False)
        self.entities_tree.heading("Start", text="Start", command=lambda: self._treeview_sort_column(self.entities_tree, "Start", False))
        self.entities_tree.heading("End", text="End", command=lambda: self._treeview_sort_column(self.entities_tree, "End", False))
        self.entities_tree.heading("Text", text="Text", command=lambda: self._treeview_sort_column(self.entities_tree, "Text", False))
        self.entities_tree.heading("Tag", text="Tag", command=lambda: self._treeview_sort_column(self.entities_tree, "Tag", False))
        self.entities_tree.column("Start", width=70, anchor=tk.W, stretch=False)
        self.entities_tree.column("End", width=70, anchor=tk.W, stretch=False)
        self.entities_tree.column("Text", width=300, anchor=tk.W, stretch=True)
        self.entities_tree.column("Tag", width=100, anchor=tk.W, stretch=False)
        self.entities_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.entities_tree.bind("<<TreeviewSelect>>", self.on_entity_select)
        self.entities_tree.bind("<Key>", lambda event: self._treeview_key_navigate(self.entities_tree, event))
        self.entities_tree.bind("<Delete>", self.remove_entity_annotation)
        scrollbar_entities_y.config(command=self.entities_tree.yview)

        relations_list_frame = tk.LabelFrame(list_panel, text="Relations", padx=5, pady=5)
        list_panel.add(relations_list_frame, stretch="always", minsize=75)
        relations_tree_frame = tk.Frame(relations_list_frame)
        relations_tree_frame.pack(fill=tk.BOTH, expand=True)
        scrollbar_relations_y = tk.Scrollbar(relations_tree_frame)
        scrollbar_relations_y.pack(side=tk.RIGHT, fill=tk.Y)
        self.relations_tree = ttk.Treeview(relations_tree_frame, columns=("ID", "Head", "Type", "Tail"),
                                           displaycolumns=("Head", "Type", "Tail"), show="headings",
                                           yscrollcommand=scrollbar_relations_y.set, selectmode='browse')
        self.relations_tree.column("ID", width=0, stretch=False)
        self.relations_tree.heading("Head", text="Head Entity", command=lambda: self._treeview_sort_column(self.relations_tree, "Head", False))
        self.relations_tree.heading("Type", text="Relation Type", command=lambda: self._treeview_sort_column(self.relations_tree, "Type", False))
        self.relations_tree.heading("Tail", text="Tail Entity", command=lambda: self._treeview_sort_column(self.relations_tree, "Tail", False))
        self.relations_tree.column("Head", width=250, anchor=tk.W, stretch=True)
        self.relations_tree.column("Type", width=120, anchor=tk.CENTER, stretch=False)
        self.relations_tree.column("Tail", width=250, anchor=tk.W, stretch=True)
        self.relations_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.relations_tree.bind("<<TreeviewSelect>>", self.on_relation_select)
        self.relations_tree.bind("<Key>", lambda event: self._treeview_key_navigate(self.relations_tree, event))
        self.relations_tree.bind("<Delete>", self.remove_relation_annotation)
        scrollbar_relations_y.config(command=self.relations_tree.yview)

    def _treeview_sort_column(self, tree, col, reverse):
        items = tree.get_children("")
        if col in ["Start", "End"] and tree == self.entities_tree:
            data = [(tuple(map(int, tree.set(item, col).split('.'))), item)
                    if tree.set(item, col) else ((0, 0), item) for item in items]
        else:
            data = [(tree.set(item, col).lower(), item) for item in items]

        data.sort(reverse=reverse)
        for index, (_, item) in enumerate(data): tree.move(item, "", index)
        valid_selection = [s for s in tree.selection() if tree.exists(s)]
        if valid_selection:
            tree.selection_set(valid_selection)
            tree.see(valid_selection[0])
        else:
            if tree == self.entities_tree: self.selected_entity_ids_for_relation = []
            self._update_button_states()

        for column_id in tree["displaycolumns"]:
            tree.heading(column_id, text=tree.heading(column_id, 'text').replace(" ▲", "").replace(" ▼", ""))
        indicator = "▼" if reverse else "▲"
        tree.heading(col, text=f"{tree.heading(col, 'text').replace(' ▲', '').replace(' ▼', '')} {indicator}",
                     command=lambda c=col: self._treeview_sort_column(tree, c, not reverse))

    def _treeview_key_navigate(self, tree, event):
        if not event.char or not event.char.isprintable() or len(event.char) != 1: return
        char = event.char.lower()
        all_items = tree.get_children("")
        if not all_items: return
        focused_item = tree.focus()
        current_idx = all_items.index(focused_item) if focused_item else -1
        match_column = "Text" if tree == self.entities_tree else "Head"
        start_idx = (current_idx + 1) % len(all_items)
        for i in range(len(all_items)):
            check_idx = (start_idx + i) % len(all_items)
            item_id = all_items[check_idx]
            item_text = str(tree.set(item_id, match_column)).lower()
            if item_text.startswith(char):
                tree.selection_set(item_id)
                tree.focus(item_id)
                tree.see(item_id)
                if tree == self.entities_tree: self.on_entity_select(None)
                else: self.on_relation_select(None)
                return "break"

    def _on_highlight_release(self, event):
        if not self.current_file_path: return
        CLICK_TIME_THRESHOLD = 0.5
        CLICK_MOVE_THRESHOLD = 10
        time_diff = time.time() - self._click_time
        move_diff = abs(event.x - self._click_pos[0]) + abs(event.y - self._click_pos[1])
        try:
            sel_start = self.text_area.index(tk.SEL_FIRST)
            sel_end = self.text_area.index(tk.SEL_LAST)
            if sel_start != sel_end:
                self.annotate_selection()
                return
        except tk.TclError: pass

        if time_diff < CLICK_TIME_THRESHOLD and move_diff < CLICK_MOVE_THRESHOLD:
            if self._just_double_clicked:
                self._just_double_clicked = False
                return
            original_state = self.text_area.cget('state')
            self.text_area.config(state=tk.NORMAL)
            try:
                click_index_str = self.text_area.index(f"@{event.x},{event.y}")
                click_pos = tuple(map(int, click_index_str.split('.')))
                entities = self.annotations.get(self.current_file_path, {}).get("entities", [])

                sorted_entities = sorted(entities, key=lambda e: (e['start_line'], e['start_char']))
                start_positions = [(e['start_line'], e['start_char']) for e in sorted_entities]
                idx = bisect_left(start_positions, click_pos)
                clicked_entity_dict = None

                for i in range(max(0, idx - 1), min(len(sorted_entities), idx + 1)):
                    entity = sorted_entities[i]
                    start_pos_tuple = (entity['start_line'], entity['start_char'])
                    end_pos_tuple = (entity['end_line'], entity['end_char'])
                    if start_pos_tuple <= click_pos < end_pos_tuple:
                        clicked_entity_dict = entity
                        break

                if clicked_entity_dict:
                    self._remove_entity_instance(clicked_entity_dict)
            except (tk.TclError, ValueError): pass
            finally:
                if self.text_area.winfo_exists():
                    self.text_area.config(state=original_state)

    def _on_double_click(self, event):
        self._just_double_clicked = True
        if not self.current_file_path: return "break"
        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL)
        try:
            click_index_str = self.text_area.index(f"@{event.x},{event.y}")
            click_pos = tuple(map(int, click_index_str.split('.')))
            entities = self.annotations.get(self.current_file_path, {}).get("entities", [])

            sorted_entities = sorted(entities, key=lambda e: (e['start_line'], e['start_char']))
            start_positions = [(e['start_line'], e['start_char']) for e in sorted_entities]
            idx = bisect_left(start_positions, click_pos)
            for i in range(max(0, idx - 1), min(len(sorted_entities), idx + 1)):
                entity = sorted_entities[i]
                start_pos = (entity['start_line'], entity['start_char'])
                end_pos = (entity['end_line'], entity['end_char'])
                if start_pos <= click_pos < end_pos:
                    return "break"

            word_start = self.text_area.index(f"{click_index_str} wordstart")
            word_end = self.text_area.index(f"{click_index_str} wordend")
            if word_start != word_end:
                self.text_area.tag_remove(tk.SEL, "1.0", tk.END)
                self.text_area.tag_add(tk.SEL, word_start, word_end)
                self.annotate_selection()
        except (tk.TclError, ValueError): pass
        finally:
            if self.text_area.winfo_exists():
                self.text_area.config(state=original_state)
        return "break"

    def _remove_entity_instance(self, entity_to_remove):
        if not self.current_file_path or self.current_file_path not in self.annotations: return
        self._handle_entity_deletion([entity_to_remove])

    def get_color_for_tag(self, tag):
        if tag not in self.tag_colors:
            try:
                if tag in self.entity_tags: self.tag_colors[tag] = next(self.color_cycle)
                else: return "#cccccc"
            except Exception: self.tag_colors[tag] = "#cccccc"
        return self.tag_colors.get(tag, "#cccccc")

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

    def load_directory(self):
        if self._has_unsaved_changes():
            if not messagebox.askyesno("Unsaved Changes", "You have unsaved changes.\nDiscard and load new directory?", parent=self.root): return
        directory = filedialog.askdirectory(title="Select Directory with Text Files")
        if directory:
            new_files_list = []
            try:
                for filename in sorted(os.listdir(directory)):
                    if filename.lower().endswith(".txt") and os.path.isfile(os.path.join(directory, filename)):
                        new_files_list.append(os.path.join(directory, filename))
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
                self.status_var.set(f"Loaded {len(self.files_list)} files from '{os.path.basename(directory)}'")
                self.root.title(f"ANNIE - {os.path.basename(directory)}")
            else:
                self.status_var.set(f"No .txt files found in '{os.path.basename(directory)}'")
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
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")],
            parent=self.root)
        if not source_paths: return
        destination_dir = os.path.dirname(self.files_list[0])
        current_basenames = {os.path.basename(p) for p in self.files_list}
        added_count = 0
        for source_path in source_paths:
            basename = os.path.basename(source_path)
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
            self.status_var.set(f"Successfully added {added_count} file(s) to the session.")

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

    def _load_api_keys(self):
        self.hf_api_key = ""
        self.claude_api_key = ""
        self.openai_api_key = ""
        self.together_api_key = ""

        env_path = Path(".env")
        if env_path.exists():
            with open(env_path, "r", encoding="utf-8") as f:
                for line in f:
                    line = line.strip()
                    if not line or line.startswith("#"): continue
                    if "=" in line:
                        key, val = line.split("=", 1)
                        key, val = key.strip(), val.strip()
                        if key == "HF_API_KEY": self.hf_api_key = val
                        elif key == "CLAUDE_API_KEY": self.claude_api_key = val
                        elif key == "OPENAI_API_KEY": self.openai_api_key = val
                        elif key == "TOGETHER_API_KEY": self.together_api_key = val

    def _save_api_keys(self):
        env_path = Path(".env")
        existing_lines = []
        if env_path.exists():
            with open(env_path, "r", encoding="utf-8") as f:
                existing_lines = f.readlines()

        keys_to_save = {
            "HF_API_KEY": self.hf_api_key,
            "CLAUDE_API_KEY": self.claude_api_key,
            "OPENAI_API_KEY": self.openai_api_key,
            "TOGETHER_API_KEY": self.together_api_key
        }

        new_lines = []
        for line in existing_lines:
            stripped = line.strip()
            if stripped and not stripped.startswith("#") and "=" in stripped:
                k, _ = stripped.split("=", 1)
                k = k.strip()
                if k in keys_to_save:
                    if keys_to_save[k]:
                        new_lines.append(f"{k}={keys_to_save[k]}\n")
                    del keys_to_save[k]
                else:
                    new_lines.append(line)
            else:
                new_lines.append(line)

        for k, v in keys_to_save.items():
            if v:
                new_lines.append(f"{k}={v}\n")

        with open(env_path, "w", encoding="utf-8") as f:
            f.writelines(new_lines)

    def _build_entity_lookup_map(self, entities):
        self._entity_lookup_map.clear()
        for entity in entities:
            key = (entity['id'], entity['start_line'], entity['start_char'],
                   entity['end_line'], entity['end_char'], entity['tag'])
            self._entity_lookup_map[key] = entity

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

    def import_annotations(self):
        import_path = filedialog.askopenfilename(
            title="Select Annotation File to Import",
            filetypes=[("All Supported Formats", "*.conll *.jsonl"), ("CoNLL Files", "*.conll"), ("JSONL Files", "*.jsonl")],
            parent=self.root)
        if not import_path: return
        try:
            parsed_docs, found_tags = [], set()
            if import_path.lower().endswith(".conll"): parsed_docs, found_tags = self._parse_conll_into_documents(import_path)
            elif import_path.lower().endswith(".jsonl"): parsed_docs, found_tags = self._parse_jsonl_into_documents(import_path)
            else:
                messagebox.showwarning("Unsupported Format", "Please select a .conll or .jsonl file.")
                return
            if not parsed_docs:
                messagebox.showinfo("Info", "No valid documents found in the import file.", parent=self.root)
                return
            new_tags = found_tags - set(self.entity_tags)
            if new_tags:
                if messagebox.askyesno("New Tags Found", f"Found new tags: {', '.join(new_tags)}.\n\nAdd them to the session?"):
                    if "Imported Tags" not in self.tag_hierarchy: self.tag_hierarchy["Imported Tags"] = []
                    for t in new_tags:
                        self.tag_hierarchy["Imported Tags"].append(t)
                        self.tag_active_states[t] = True
                        self.tag_propagation_states[t] = True
                    self._sync_flat_tags()
                    self._update_entity_tag_combobox()
                    self._configure_text_tags()
                else:
                    approved_tags = set(self.entity_tags)
                    for doc in parsed_docs:
                        doc['annotations'] = [ann for ann in doc['annotations'] if ann['tag'] in approved_tags]
            save_dir = self._ask_for_save_directory(os.path.dirname(import_path))
            if not save_dir: return
            os.makedirs(save_dir, exist_ok=True)
            if not self.files_list and parsed_docs: self._reset_state()
            base_name_for_docs = os.path.basename(os.path.splitext(import_path)[0])
            new_file_paths = []
            for i, doc in enumerate(parsed_docs):
                save_path = os.path.join(save_dir, f"{base_name_for_docs}_{i + 1}.txt")
                with open(save_path, 'w', encoding='utf-8') as f: f.write(doc['text'])
                self.files_list.append(save_path)
                new_file_paths.append(save_path)
                final_annotations = []
                line_starts = [0]
                for j, char in enumerate(doc['text']):
                    if char == '\n': line_starts.append(j + 1)
                line_starts.append(len(doc['text']) + 1)

                for ann in doc['annotations']:
                    start_pos_str = self._char_offset_to_tkinter_index_from_offsets(line_starts, ann['start'])
                    end_pos_str = self._char_offset_to_tkinter_index_from_offsets(line_starts, ann['end'])
                    start_line, start_char = map(int, start_pos_str.split('.'))
                    end_line, end_char = map(int, end_pos_str.split('.'))
                    text = doc['text'][ann['start']:ann['end']]
                    final_annotations.append({'id': uuid.uuid4().hex, 'start_line': start_line, 'start_char': start_char,
                                              'end_line': end_line, 'end_char': end_char, 'text': text, 'tag': ann['tag']})
                self.annotations[save_path] = {"entities": final_annotations, "relations": []}
            self.files_listbox.delete(0, tk.END)
            for path in self.files_list: self.files_listbox.insert(tk.END, os.path.basename(path))
            self.load_file(len(self.files_list) - len(new_file_paths))
            self.status_var.set(f"Successfully imported {len(parsed_docs)} documents.")
        except Exception as e:
            messagebox.showerror("Import Error", f"An error occurred during import:\n{e}", parent=self.root)
            traceback.print_exc()

    def _char_offset_to_tkinter_index_from_offsets(self, line_offsets, offset):
        line_idx = bisect_right(line_offsets, offset) - 1
        line = line_idx + 1
        char = offset - line_offsets[line_idx]
        return f"{line}.{char}"

    def _parse_conll_into_documents(self, file_path):
        with open(file_path, 'r', encoding='utf-8') as f: content = f.read()
        doc_chunks = re.split(r'\n\s*\n|-DOCSTART-.*\n', content)
        documents, all_tags = [], set()
        for chunk in doc_chunks:
            if not chunk.strip(): continue
            doc_lines = chunk.strip().splitlines()
            text, annotations, tags = self._process_conll_chunk(doc_lines)
            if text.strip():
                documents.append({'text': text, 'annotations': annotations})
                all_tags.update(tags)
        return documents, all_tags

    def _parse_jsonl_into_documents(self, file_path):
        documents, all_tags = [], set()
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read().strip()
            json_objects_str = content.replace('}{', '}\n{').splitlines()
            for line in json_objects_str:
                if not line.strip(): continue
                data = json.loads(line)
                text = data.get("text")
                spans = data.get("spans", [])
                if text:
                    annotations = []
                    for span in spans:
                        start = span.get("start")
                        end = span.get("end")
                        tag = span.get("label")
                        if start is not None and end is not None and tag is not None:
                            annotations.append({'start': start, 'end': end, 'tag': tag})
                            all_tags.add(tag)
                    documents.append({'text': text, 'annotations': annotations})
        return documents, all_tags

    def _process_conll_chunk(self, lines):
        reconstructed_text = ""
        annotations = []
        found_tags = set()
        current_char = 0
        current_entity = None
        for line in lines:
            line = line.strip()
            if not line:
                if reconstructed_text and not reconstructed_text.endswith(('\n', ' ')):
                    reconstructed_text += "\n"
                    current_char += 1
                if current_entity: annotations.append(current_entity)
                current_entity = None
                continue
            parts = line.split()
            if len(parts) < 2: continue
            token, tag = parts[0], parts[-1]
            if reconstructed_text and not reconstructed_text.endswith('\n'):
                reconstructed_text += " "
                current_char += 1
            start_char = current_char
            reconstructed_text += token
            current_char += len(token)
            end_char = current_char
            if tag.startswith("B-"):
                if current_entity: annotations.append(current_entity)
                tag_name = tag[2:]
                found_tags.add(tag_name)
                current_entity = {'tag': tag_name, 'start': start_char, 'end': end_char}
            elif tag.startswith("I-") and current_entity and tag[2:] == current_entity['tag']:
                current_entity['end'] = end_char
            else:
                if current_entity: annotations.append(current_entity)
                current_entity = None
        if current_entity: annotations.append(current_entity)
        return reconstructed_text, annotations, found_tags

    def _spans_overlap_numeric(self, start1_l, start1_c, end1_l, end1_c, start2_l, start2_c, end2_l, end2_c):
        span1_start, span1_end = (start1_l, start1_c), (end1_l, end1_c)
        span2_start, span2_end = (start2_l, start2_c), (end2_l, end2_c)
        return not ((span1_end <= span2_start) or (span1_start >= span2_end))

    def _is_overlapping_in_list(self, start_l, start_c, end_l, end_c, entities_list):
        for ann in entities_list:
            if self._spans_overlap_numeric(start_l, start_c, end_l, end_c, ann['start_line'], ann['start_char'], ann['end_line'], ann['end_char']): return True
        return False

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

    def _add_to_entity_lookup_map(self, entity):
        key = (entity['id'], entity['start_line'], entity['start_char'],
               entity['end_line'], entity['end_char'], entity['tag'])
        self._entity_lookup_map[key] = entity

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

    def on_relation_select(self, event=None):
        self._update_button_states()

    def propagate_annotations(self):
        if not self.current_file_path: return
        source_entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        if not source_entities: return
        allowed_tags = {tag for tag, allowed in self.tag_propagation_states.items() if allowed}
        filtered_entities = [ann for ann in source_entities if ann['tag'] in allowed_tags]
        if not filtered_entities: return
        text_to_tag = {ann['text'].strip(): ann['tag'] for ann in sorted(filtered_entities, key=lambda a: (a['start_line'], a['start_char'])) if ann['text'].strip()}
        if not text_to_tag: return
        if not messagebox.askyesno("Confirm Propagation", f"Propagate {len(text_to_tag)} unique entities across all files?", parent=self.root): return
        self._perform_propagation(text_to_tag, "Current File Propagation")

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
        if not messagebox.askyesno("Confirm Propagation", f"Propagate {len(dictionary_mapping)} entities from dictionary?", parent=self.root): return
        self._perform_propagation(dictionary_mapping, "Dictionary Propagation")

    def _perform_propagation(self, text_to_tag_map, source_description):
        propagated_count, affected_files = 0, set()
        allow_overlap = True if "Dictionary" in source_description else self.allow_multilabel_overlap.get()
        self.status_var.set(f"Starting {source_description}..."); self.root.update()
        file_contents = {}
        for file_path in self.files_list:
            try:
                with open(file_path, 'r', encoding='utf-8') as f: file_contents[file_path] = f.read()
            except Exception: continue

        compiled_regexes = []
        for text, tag in text_to_tag_map.items():
            pattern = r'\b' + re.escape(text) + r'\b'
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
                    matched_text = match.group()
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

    def manage_entity_tags(self):
        window = tk.Toplevel(self.root)
        window.title("Manage Layered Entity Tags")
        window.geometry("650x550")
        window.transient(self.root)
        window.grab_set()

        list_frame = tk.Frame(window)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(10, 5))

        columns = ("Count", "Active", "Propagate")
        tree = ttk.Treeview(list_frame, columns=columns, selectmode="browse")
        tree.heading("#0", text="Layer / Tag", anchor=tk.W)
        tree.heading("Count", text="Count", anchor=tk.CENTER)
        tree.heading("Active", text="Active (Hotkeys)", anchor=tk.CENTER)
        tree.heading("Propagate", text="Auto-Propagate", anchor=tk.CENTER)

        tree.column("#0", width=250, anchor=tk.W)
        tree.column("Count", width=60, anchor=tk.CENTER)
        tree.column("Active", width=130, anchor=tk.CENTER)
        tree.column("Propagate", width=120, anchor=tk.CENTER)

        scrollbar = tk.Scrollbar(list_frame, orient=tk.VERTICAL, command=tree.yview)
        tree.configure(yscrollcommand=scrollbar.set)
        tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        def refresh_tree():
            tree.delete(*tree.get_children())
            hotkey_counter = 1

            tag_counts = {}
            for file_path, data in self.annotations.items():
                for entity in data.get("entities", []):
                    t = entity.get("tag")
                    if t: tag_counts[t] = tag_counts.get(t, 0) + 1

            for layer, tags in self.tag_hierarchy.items():
                layer_active = any(self.tag_active_states.get(t, True) for t in tags)
                layer_prop = any(self.tag_propagation_states.get(t, True) for t in tags)
                l_act = "✅ (Layer)" if layer_active else "❌ (Layer)"
                l_prop = "✅ (Layer)" if layer_prop else "❌ (Layer)"
                layer_count = sum(tag_counts.get(t, 0) for t in tags)

                layer_iid = tree.insert("", tk.END, text=layer, values=(layer_count, l_act, l_prop), open=True)

                for tag in tags:
                    is_active = self.tag_active_states.get(tag, True)
                    is_prop = self.tag_propagation_states.get(tag, True)
                    act_display = "❌"
                    if is_active:
                        if hotkey_counter <= 10:
                            num = hotkey_counter if hotkey_counter < 10 else 0
                            act_display = f"✅ (Key: {num})"
                            hotkey_counter += 1
                        else: act_display = "✅ (No key)"

                    prop_display = "✅" if is_prop else "❌"
                    count = tag_counts.get(tag, 0)
                    tid = tree.insert(layer_iid, tk.END, text=tag, values=(count, act_display, prop_display))

                    color = self.get_color_for_tag(tag)
                    try: tree.tag_configure(tid, background=color)
                    except: pass
                    tree.item(tid, tags=(tid,))

        refresh_tree()

        def on_tree_double_click(event):
            item_id = tree.identify_row(event.y)
            column = tree.identify_column(event.x)
            if not item_id or column not in ('#2', '#3'): return

            item_text = tree.item(item_id, 'text')
            parent_id = tree.parent(item_id)
            is_layer = (parent_id == '')

            if column == '#2':
                if is_layer:
                    current_active = any(self.tag_active_states.get(t, True) for t in self.tag_hierarchy[item_text])
                    for t in self.tag_hierarchy[item_text]: self.tag_active_states[t] = not current_active
                else: self.tag_active_states[item_text] = not self.tag_active_states.get(item_text, True)
            elif column == '#3':
                if is_layer:
                    current_prop = any(self.tag_propagation_states.get(t, True) for t in self.tag_hierarchy[item_text])
                    for t in self.tag_hierarchy[item_text]: self.tag_propagation_states[t] = not current_prop
                else: self.tag_propagation_states[item_text] = not self.tag_propagation_states.get(item_text, True)

            refresh_tree()
            self._update_entity_tag_combobox()

        tree.bind("<Double-1>", on_tree_double_click)

        controls_frame = tk.Frame(window)
        controls_frame.pack(fill=tk.X, padx=10, pady=10)
        add_frame = tk.Frame(controls_frame)
        add_frame.pack(fill=tk.X, pady=5)
        tk.Label(add_frame, text="New Tag:").pack(side=tk.LEFT)
        new_tag_var = tk.StringVar()
        entry = tk.Entry(add_frame, textvariable=new_tag_var)
        entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)

        def add_tag():
            tag = new_tag_var.get().strip()
            if not tag: return
            if tag in self.entity_tags:
                messagebox.showwarning("Duplicate", "Tag already exists!", parent=window)
                return

            selected = tree.selection()
            if selected:
                item_id = selected[0]
                parent_id = tree.parent(item_id)
                target_layer = tree.item(item_id, 'text') if parent_id == '' else tree.item(parent_id, 'text')
            else: target_layer = list(self.tag_hierarchy.keys())[0]

            self.tag_hierarchy[target_layer].append(tag)
            self.tag_active_states[tag] = True
            self.tag_propagation_states[tag] = True
            self._sync_flat_tags()
            refresh_tree()
            self._update_entity_tag_combobox()
            new_tag_var.set("")

        tk.Button(add_frame, text="Add to Selected Layer", command=add_tag).pack(side=tk.LEFT)
        entry.bind("<Return>", lambda e: add_tag())

        btn_frame = tk.Frame(controls_frame)
        btn_frame.pack(fill=tk.X, pady=5)

        def rename_tag():
            selected = tree.selection()
            if not selected: return
            item_id = selected[0]
            if tree.parent(item_id) == '':
                messagebox.showinfo("Info", "Cannot rename entire layers yet, select a Tag.", parent=window)
                return

            old_tag = tree.item(item_id, 'text')
            from tkinter import simpledialog
            new_tag = simpledialog.askstring("Rename / Merge Tag", f"New name for '{old_tag}':\n(If you type an existing tag, they will be merged)", initialvalue=old_tag, parent=window)
            if not new_tag: return
            new_tag = new_tag.strip()
            if not new_tag or new_tag == old_tag: return

            parent_layer = tree.item(tree.parent(item_id), 'text')

            if new_tag in self.entity_tags:
                if not messagebox.askyesno("Merge Tags", f"The tag '{new_tag}' already exists.\n\nDo you want to MERGE all '{old_tag}' annotations into '{new_tag}'?\n\nThis will remove '{old_tag}' from the list entirely.", parent=window): return
                self.tag_hierarchy[parent_layer].remove(old_tag)
                self.tag_active_states.pop(old_tag, None)
                self.tag_propagation_states.pop(old_tag, None)
                self.tag_colors.pop(old_tag, None)
                self._sync_flat_tags()

                rename_count = 0
                for file_path, data in self.annotations.items():
                    for entity in data.get("entities", []):
                        if entity.get("tag") == old_tag:
                            entity["tag"] = new_tag
                            rename_count += 1
                if self.current_file_path: self._build_entity_lookup_map(self.annotations.get(self.current_file_path, {}).get('entities', []))
                messagebox.showinfo("Merge Successful", f"Successfully merged '{old_tag}' into '{new_tag}'.\nUpdated {rename_count} annotations.", parent=window)
            else:
                idx = self.tag_hierarchy[parent_layer].index(old_tag)
                self.tag_hierarchy[parent_layer][idx] = new_tag
                self.tag_active_states[new_tag] = self.tag_active_states.pop(old_tag, True)
                self.tag_propagation_states[new_tag] = self.tag_propagation_states.pop(old_tag, True)
                if old_tag in self.tag_colors: self.tag_colors[new_tag] = self.tag_colors.pop(old_tag)
                self._sync_flat_tags()

                rename_count = 0
                for file_path, data in self.annotations.items():
                    for entity in data.get("entities", []):
                        if entity.get("tag") == old_tag:
                            entity["tag"] = new_tag
                            rename_count += 1
                if self.current_file_path: self._build_entity_lookup_map(self.annotations.get(self.current_file_path, {}).get('entities', []))
                messagebox.showinfo("Rename Successful", f"Renamed to '{new_tag}'.\nUpdated {rename_count} annotations.", parent=window)

            refresh_tree()
            self._update_entity_tag_combobox()

        tk.Button(btn_frame, text="Rename Selected", command=rename_tag).pack(side=tk.LEFT)
        tk.Label(btn_frame, text="(Double-click columns to toggle Active/Propagate)", fg="grey").pack(side=tk.LEFT, padx=10)

        def save_and_close():
            self._configure_text_tags()
            if self.current_file_path:
                self.apply_annotations_to_text()
                self.update_entities_list()
            window.destroy()

        tk.Button(btn_frame, text="Close", command=save_and_close, width=10).pack(side=tk.RIGHT)
        window.wait_window()

    def manage_relation_types(self):
        self._manage_items("Relation Types", self.relation_types, self._update_relation_type_combobox)

    def _manage_items(self, item_type_name, current_items_list, update_combobox_func):
        window = tk.Toplevel(self.root); window.title(f"Manage {item_type_name}")
        window.geometry("350x400"); window.minsize(300, 250)
        window.transient(self.root); window.grab_set()
        list_frame = tk.Frame(window); list_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(10, 0))
        tk.Label(list_frame, text=f"Current {item_type_name}:").pack(anchor=tk.W)
        scrollbar = tk.Scrollbar(list_frame); scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        listbox = tk.Listbox(list_frame, yscrollcommand=scrollbar.set, exportselection=False, selectmode=tk.EXTENDED)
        current_items_list.sort(key=str.lower)
        for index, item in enumerate(current_items_list):
            display_text = item
            if item_type_name == "Entity Tags" and index < 10:
                hotkey_num = (index + 1) % 10 if (index + 1) % 10 != 0 else 0
                display_text = f"{hotkey_num}: {item}"
            listbox.insert(tk.END, display_text)
        listbox.pack(fill=tk.BOTH, expand=True); scrollbar.config(command=listbox.yview)
        controls_frame = tk.Frame(window); controls_frame.pack(fill=tk.X, padx=10, pady=5)
        item_var = tk.StringVar()
        item_entry = tk.Entry(controls_frame, textvariable=item_var, width=20)
        item_entry.grid(row=0, column=0, sticky="ew", padx=(0, 5))
        controls_frame.grid_columnconfigure(0, weight=1)
        def add_item():
            item = item_var.get().strip()
            if item:
                raw_items = list(listbox.get(0, tk.END))
                existing = [re.sub(r"^\d:\s", "", i).lower() for i in raw_items]
                if item.lower() not in existing:
                    listbox.insert(tk.END, item)
                    updated_items = list(listbox.get(0, tk.END))
                    listbox.delete(0, tk.END)
                    for i_val in sorted(updated_items, key=str.lower): listbox.insert(tk.END, i_val)
                    item_var.set("")
                else: messagebox.showwarning("Duplicate", f"'{item}' already exists.", parent=window)
            item_entry.focus_set()
        item_entry.bind("<Return>", lambda event: add_item())
        tk.Button(controls_frame, text="Add", width=7, command=add_item).grid(row=0, column=1, padx=5)
        def remove_item():
            indices = listbox.curselection()
            if indices:
                for index in sorted(indices, reverse=True): listbox.delete(index)
            else: messagebox.showwarning("No Selection", "Select item(s) to remove.", parent=window)
        tk.Button(controls_frame, text="Remove", width=7, command=remove_item).grid(row=0, column=2)
        button_frame = tk.Frame(window); button_frame.pack(fill=tk.X, padx=10, pady=(5, 10))
        def save_changes():
            new_items_raw = list(listbox.get(0, tk.END))
            new_items = new_items_raw if item_type_name != "Entity Tags" else [re.sub(r"^\d:\s*", "", item) for item in new_items_raw]
            if set(new_items) != set(current_items_list):
                current_items_list[:] = new_items
                update_combobox_func()
                if item_type_name == "Relation Types": self.update_relations_list()
            window.destroy()
        tk.Button(button_frame, text="Save Changes", width=12, command=save_changes).pack(side=tk.RIGHT, padx=5)
        tk.Button(button_frame, text="Cancel", width=12, command=window.destroy).pack(side=tk.RIGHT)
        item_entry.focus_set()
        window.wait_window()

    # =========================================================================
    # ENSEMBLE AI & PREDICTION LOGIC (Merged Session Memory + HF Neural Model)
    # =========================================================================

    def predict_from_session_memory(self):
        """Manual button: Predicts using ONLY Session Memory (Knowledge Base)."""
        if not self.current_file_path:
            messagebox.showwarning("Nincs fájl", "Kérlek, tölts be egy oklevelet!", parent=self.root)
            return

        self.status_var.set("Session Memory elemzése...")
        self.progress_bar.start()
        self.root.update()

        try:
            with open(self.current_file_path, 'r', encoding='utf-8') as f: content = f.read()
        except Exception as e:
            self.progress_bar.stop()
            messagebox.showerror("Hiba", f"Nem sikerült beolvasni a fájlt:\n{e}", parent=self.root)
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
        mapping_outer_frame.pack(fill=tk.BOTH, expand=True) # expand=True engedi, hogy kitöltse a helyet

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

    def _update_status_threadsafe(self, message):
        self.ai_status_queue.put(message)

    def _process_queue(self):
        try:
            while True:
                message = self.ai_status_queue.get_nowait()

                # Check for explicit DONE signal to stop progress bar
                if message.startswith("DONE|"):
                    self.status_var.set(message.split("|", 1)[1])
                    self.progress_bar.stop()
                    try: self.settings_menu.entryconfig("Pre-annotate with Hybrid AI...", state="normal")
                    except: pass
                else:
                    self.status_var.set(message)
                    self.progress_bar.start()

                self.root.update()
        except queue.Empty: pass
        self.root.after(100, self._process_queue)

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
                # Automatikusan 1:1-ben megfelelteti a HF címkéket a program címkéinek, ha aktívak
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


    def _retrieve_similar_examples(self, query_text, top_k):
        """
        RAG: TF-IDF
        """
        corpus_docs = []
        corpus_data = []

        for fp, data in self.annotations.items():
            if fp == self.current_file_path: continue
            entities = data.get('entities', [])
            if not entities: continue

            try:
                with open(fp, 'r', encoding='utf-8') as f:
                    text = f.read()
            except Exception:
                continue

            corpus_docs.append(text)
            corpus_data.append((text, entities))

        if not corpus_docs:
            return []

        def tokenize(t):
            return re.findall(r'\w+', t.lower())

        corpus_tokens = [tokenize(doc) for doc in corpus_docs]
        query_tokens = tokenize(query_text)

        if not query_tokens:
            return corpus_data[:top_k]

        N = len(corpus_tokens)
        df = Counter()
        for tokens in corpus_tokens:
            for w in set(tokens):
                df[w] += 1

        # idf(t) = log [ (1 + n) / (1 + df(d, t)) ] + 1
        idf = {w: math.log((1 + N) / (1 + df[w])) + 1 for w in df}

        def get_tfidf_vector(tokens):
            tf = Counter(tokens)
            total_words = len(tokens) if tokens else 1
            vec = {}
            for w, count in tf.items():
                w_idf = idf.get(w, math.log((1 + N) / 1) + 1) # Ha ismeretlen szó a query-ben
                vec[w] = (count / total_words) * w_idf
            return vec

        query_vec = get_tfidf_vector(query_tokens)
        corpus_vecs = [get_tfidf_vector(tokens) for tokens in corpus_tokens]

        def cosine_sim(v1, v2):
            intersection = set(v1.keys()) & set(v2.keys())
            dot_product = sum(v1[w] * v2[w] for w in intersection)
            norm_v1 = math.sqrt(sum(val**2 for val in v1.values()))
            norm_v2 = math.sqrt(sum(val**2 for val in v2.values()))
            if norm_v1 == 0 or norm_v2 == 0: return 0.0
            return dot_product / (norm_v1 * norm_v2)

        scores = [(cosine_sim(query_vec, cv), data) for cv, data in zip(corpus_vecs, corpus_data)]
        scores.sort(key=lambda x: x[0], reverse=True)

        return [data for score, data in scores[:top_k]]

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

    # =========================================================================
    # GLOBAL SEARCH LOGIC
    # =========================================================================

    def find_text_dialog(self, event=None):
        from tkinter import simpledialog
        search_term = simpledialog.askstring("Global Search", "Search term in entire session:", parent=self.root)
        if search_term: self._search_text_globally(search_term)

    def _search_text_globally(self, term):
        if not self.files_list:
            messagebox.showinfo("Search", "No files loaded in session.", parent=self.root)
            return
        matching_files = []
        term_lower = term.lower()
        self.status_var.set(f"Search in progress: '{term}'...")
        self.root.update()

        for idx, file_path in enumerate(self.files_list):
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read().lower()
                    if term_lower in content: matching_files.append((idx, file_path))
            except Exception: continue

        if not matching_files:
            self.status_var.set("Search complete.")
            messagebox.showinfo("Search", f"No results found in the entire session for the following:\n'{term}'", parent=self.root)
            return
        self.status_var.set(f"Found in {len(matching_files)} files.")
        self._show_search_results(term, matching_files)

    def _show_search_results(self, term, matching_files):
        results_window = tk.Toplevel(self.root)
        results_window.title(f"Search result: '{term}'")
        results_window.geometry("500x300")
        results_window.transient(self.root)
        tk.Label(results_window, text=f"{len(matching_files)} found in the document/sentence:").pack(anchor=tk.W, padx=10, pady=5)
        list_frame = tk.Frame(results_window)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        scrollbar = tk.Scrollbar(list_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        results_listbox = tk.Listbox(list_frame, yscrollcommand=scrollbar.set)
        results_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.config(command=results_listbox.yview)

        for idx, file_path in matching_files:
            display_name = os.path.basename(file_path)
            results_listbox.insert(tk.END, f"[{idx + 1}] {display_name}")

        def on_result_double_click(event):
            selection = results_listbox.curselection()
            if not selection: return
            listbox_idx = selection[0]
            file_idx = matching_files[listbox_idx][0]
            self.load_file(file_idx)
            self._highlight_term_in_current_file(term)

        results_listbox.bind("<Double-Button-1>", on_result_double_click)
        tk.Label(results_window, text="Double-click on the file to open and highlight it.", fg="grey").pack(pady=5)

    def _highlight_term_in_current_file(self, term):
        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL)
        try:
            self.text_area.tag_remove('search_highlight', '1.0', tk.END)
            self.text_area.tag_config('search_highlight', background='yellow', foreground='black')
            start_pos = '1.0'
            first_match = None
            while True:
                start_pos = self.text_area.search(term, start_pos, stopindex=tk.END, nocase=True)
                if not start_pos: break
                end_pos = f"{start_pos}+{len(term)}c"
                self.text_area.tag_add('search_highlight', start_pos, end_pos)
                if first_match is None: first_match = start_pos
                start_pos = end_pos
            if first_match:
                self.text_area.see(first_match)
                self.status_var.set(f"Highlights: '{term}'")
        finally:
            if self.text_area.winfo_exists(): self.text_area.config(state=original_state)

# =========================================================================
    # GENERATIVE LLM AGENT (Few-Shot Prompting via API)
    # =========================================================================

    def run_llm_agent_from_hotkey(self, event=None):
        """A 'g' billentyű lenyomásakor hívódik meg."""
        if getattr(self, '_is_annotating_ai', False): return
        if not self.current_file_path: return

        # Ellenőrizzük, hogy a jelenleg kiválasztott szolgáltatóhoz van-e már API kulcsunk
        key_exists = False
        if self.llm_provider == "Anthropic (Claude)" and self.claude_api_key.strip(): key_exists = True
        elif self.llm_provider == "OpenAI" and self.openai_api_key.strip(): key_exists = True
        elif self.llm_provider == "Together AI" and self.together_api_key.strip(): key_exists = True
        elif self.llm_provider == "Hugging Face" and self.hf_api_key.strip(): key_exists = True

        # Ha minden adat megvan, azonnal indítjuk az LLM-et, különben feldobjuk a beállítót
        if key_exists and self.llm_model:
            self._start_llm_agent()
        else:
            self.show_llm_settings_dialog()

    def show_llm_settings_dialog(self):
        if not self.current_file_path:
            messagebox.showwarning("Nincs fájl", "Kérlek, tölts be egy oklevelet!", parent=self.root)
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
                # Csak azokat az entitásokat kérjük, amik most aktívak a UI-n
                json_entities = [{"text": e["text"], "tag": e["tag"]} for e in entities if e["tag"] in active_tags]
                if not json_entities: continue

                prompt += f"### Example {i + 1}\nInput:\n{ex_text}\nOutput:\n{json.dumps(json_entities, ensure_ascii=False)}\n\n"

        prompt += f"### Target Task\nInput:\n{current_text}\nOutput:\n"
        return prompt

    def _start_llm_agent(self):
        if getattr(self, '_is_annotating_ai', False): return
        self._is_annotating_ai = True
        self.status_var.set(f"Generatív LLM ({self.llm_provider}) call in progress...")
        self.progress_bar.start()

        full_text = self.text_area.get("1.0", tk.END).strip()

        def thread_target():
            try:
                print(f"\n[{self.llm_provider}] Building prompt from memory...")
                prompt = self._build_few_shot_prompt(full_text)
                self._update_status_threadsafe("Waiting for LLM response...")

                result_json_str = ""

                if self.llm_provider == "OpenAI":
                    print(f"[OpenAI] Hívás: {self.llm_model} ...")
                    headers = {"Authorization": f"Bearer {self.openai_api_key}", "Content-Type": "application/json"}
                    payload = {"model": self.llm_model, "messages": [{"role": "user", "content": prompt}], "max_tokens": 4096, "temperature": 0.1}
                    response = requests.post("https://api.openai.com/v1/chat/completions", headers=headers, json=payload, timeout=(15, 300))
                    response.raise_for_status()
                    res_data = response.json()
                    result_json_str = res_data["choices"][0]["message"]["content"]

                elif self.llm_provider == "Together AI":
                    print(f"[Together AI] Hívás: {self.llm_model} ...")
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
                error_msg = f"API Hiba: {e.response.status_code}"
                try:
                    err_json = e.response.json()
                    error_msg = err_json.get('error', err_json)
                except: pass
                self._update_status_threadsafe(f"DONE|{error_msg}")
                print(f"\n[SÚLYOS API HIBA]:\n{e.response.text}\n")
            except Exception as e:
                self._update_status_threadsafe(f"DONE|Hiba: {e}")
                print(f"\n[HIBA RÉSZLETEK] {e}\n")
            finally:
                self.root.after(0, lambda: setattr(self, '_is_annotating_ai', False))

        threading.Thread(target=thread_target, daemon=True).start()

def main():
    root = tk.Tk()
    try:
        style = ttk.Style()
        themes = style.theme_names()
        preferred_themes = ['clam', 'alt', 'vista', 'xpnative']
        current_theme = style.theme_use()
        if current_theme not in preferred_themes:
            for t in preferred_themes:
                if t in themes:
                    try:
                        style.theme_use(t)
                        break
                    except tk.TclError: continue
            else:
                if 'default' in themes : style.theme_use('default')
    except tk.TclError: print("ttk themes not available or failed to apply.")
    app = TextAnnotator(root)
    root.mainloop()

if __name__ == "__main__":
    main()
