# -*- coding: utf-8 -*-
"""
ANNIE: Annotation Interface for Named-entity & Information Extraction.
Allows loading text files, annotating text spans (entities) with tags,
and annotating directed relations between entities.
Includes basic propagation for entities and management for tags/relation types.
Adds dictionary-based entity propagation, relation flipping, and entity merging.
Includes Save/Load Session functionality.
Adds Demerge functionality via text area right-click.
Adds underlining for propagated entities.
Fixes whitespace issues in propagated entities (saving & underlining).
Makes the main text area read-only to prevent accidental modification.
Double-Click/Highlight to Annotate and Single-Click to Remove.
Includes check to prevent re-annotating on double-click of existing annotation.
Adds optional multi-label annotation, allowing multiple and/or overlapping annotations.
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

# --- Constants ---
SESSION_FILE_VERSION = "1.13"


class TextAnnotator:
    """
    Handles UI creation, file loading, annotation logic, and saving.
    """
    def __init__(self, root_window):
        """
        Initializes the application.
        Sets up variables, colors, and builds the UI.
        """
        self.root = root_window
        self.root.title("ANNIE - Annotation Interface")
        self.root.geometry("1200x850")

        # --- Core Data ---
        self.current_file_path = None
        self.files_list = []
        self.current_file_index = -1
        self.annotations = {}
        self.session_save_path = None

        # --- Entity Tagging Configuration ---
        self.entity_tags = ["Person", "Organization", "Location", "Date", "Other"]
        self.selected_entity_tag = tk.StringVar(value=self.entity_tags[0] if self.entity_tags else "")
        self.extend_to_word = tk.BooleanVar(value=False)
        self.allow_multilabel_overlap = tk.BooleanVar(value=True)

        # --- Relation Tagging Configuration ---
        self.relation_types = ["spouse_of", "works_at", "located_in", "born_on", "produces"]
        self.selected_relation_type = tk.StringVar(value=self.relation_types[0] if self.relation_types else "")

        # --- UI State ---
        self.selected_entity_ids_for_relation = []
        self._entity_id_to_tree_iids = {}
        self._click_time = 0
        self._click_pos = (0, 0)
        self._is_deleting = False
        self._is_annotating_ai = False
        self._just_double_clicked = False
        self.last_used_ai_models = []  # Stores the last used models
        self.current_ai_models = [] # Current models for this session

        # --- Sort Tracking ---
        self.entities_sort_column = None
        self.entities_sort_reverse = False
        self.relations_sort_column = None
        self.relations_sort_reverse = False

        # --- Colors ---
        self.tag_colors = {
            "Person": "#ffcccc", "Organization": "#ccffcc", "Location": "#ccccff",
            "Date": "#ffffcc", "Other": "#ccffff"
        }
        self.color_cycle = itertools.cycle([
            "#e6e6fa", "#ffe4e1", "#f0fff0", "#fffacd", "#add8e6",
            "#f5f5dc", "#d3ffd3", "#fafad2", "#ffebcd", "#e0ffff"
        ])
        self._ensure_default_colors()

        # --- Build UI ---
        self.create_menu()
        self.create_layout()

        # --- Status Bar ---
        self.status_var = tk.StringVar(value="Ready. Open a directory or load a session.")
        self.status_bar = tk.Label(self.root, textvariable=self.status_var, bd=1, relief=tk.SUNKEN, anchor=tk.W)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        self.ai_status_queue = queue.Queue()
        self._process_queue()

        # --- Initial UI Setup ---
        self._update_entity_tag_combobox()
        self._update_relation_type_combobox()
        self._configure_text_tags()
        self._configure_treeview_tags()
        self._update_button_states()

        # --- Bind Hotkeys ---
        for i in range(10): # Binds keys 0-9
            self.root.bind(str(i), self._on_hotkey_press)

        # The 'a' hotkey now runs AI with the current settings without a dialog.
        self.root.bind('a', lambda event: self.run_ai_annotation_from_hotkey())

        self.root.protocol("WM_DELETE_WINDOW", self._on_closing)

    def _ensure_default_colors(self):
        for tag in self.entity_tags:
            self.get_color_for_tag(tag)

    def _on_mouse_down(self, event):
        """Records the time and position of a mouse press."""
        self._click_time = time.time()
        self._click_pos = (event.x, event.y)

    def _on_hotkey_press(self, event):
        """Handles number key presses to re-label selected entities or set the current tag."""
        try:
            key_num = int(event.keysym)
            tag_index = (key_num - 1) % 10 if key_num != 0 else 9
            if not (0 <= tag_index < len(self.entity_tags)): return

            new_tag = self.entity_tags[tag_index]
            selected_iids = self.entities_tree.selection()

            if selected_iids:
                entities_in_file = self.annotations.get(self.current_file_path, {}).get("entities", [])
                selected_iids_to_restore = list(selected_iids)

                for iid in selected_iids_to_restore:
                    try:
                        parts = iid.split('|')
                        entity_id, start_pos, end_pos, old_tag = parts[1], parts[2], parts[3], parts[4]
                        for entity_dict in entities_in_file:
                            if (entity_dict['id'] == entity_id and
                                f"{entity_dict['start_line']}.{entity_dict['start_char']}" == start_pos and
                                entity_dict['tag'] == old_tag):
                                entity_dict['tag'] = new_tag
                                break
                    except IndexError: continue

                self.apply_annotations_to_text()
                # A selection_hint-et frissített adatokkal (ID, start_pos, end_pos) kell ellátni.
                selection_info_for_rebuild = set()
                for iid in selected_iids_to_restore:
                    parts = iid.split('|')
                    entity_id, start_pos, end_pos = parts[1], parts[2], parts[3]
                    selection_info_for_rebuild.add((entity_id, start_pos, end_pos, new_tag))

                self.update_entities_list(selection_hint=selection_info_for_rebuild)
                self.status_var.set(f"Relabeled {len(selected_iids)} entit{'y' if len(selected_iids) == 1 else 'ies'} to '{new_tag}'")
            else:
                self.selected_entity_tag.set(new_tag)
                self.status_var.set(f"Selected Tag: {new_tag}")

            return "break"
        except (ValueError, IndexError):
            pass

    def create_menu(self):
        menubar = tk.Menu(self.root)

        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Open Directory", command=self.load_directory)
        file_menu.add_command(label="Add File(s) to Session...", command=self.add_files_to_session)
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
        self.settings_menu.add_command(label="Pre-annotate with AI...", command=self._show_ai_settings_dialog) # This now always opens the dialog
        self.settings_menu.add_separator()
        self.settings_menu.add_checkbutton(
            label="Allow Multi-label & Overlapping Annotations",
            variable=self.allow_multilabel_overlap,
            onvalue=True, offvalue=False
        )
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
        scrollbar_files.config(command=self.files_listbox.yview)
        nav_frame = tk.Frame(left_frame)
        nav_frame.pack(fill=tk.X, pady=5)
        self.prev_btn = tk.Button(nav_frame, text="Previous", command=self.load_previous_file, state=tk.DISABLED)
        self.prev_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0,2))
        self.next_btn = tk.Button(nav_frame, text="Next", command=self.load_next_file, state=tk.DISABLED)
        self.next_btn.pack(side=tk.RIGHT, fill=tk.X, expand=True, padx=(2,0))

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
        self.text_area = tk.Text(
            text_frame, wrap=tk.WORD,
            yscrollcommand=scrollbar_text_y.set,
            xscrollcommand=scrollbar_text_x.set,
            undo=True, state=tk.DISABLED,
            borderwidth=1, relief="sunken",
            insertbackground="black", insertwidth=2,
            takefocus=False
        )
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
        self.entities_tree = ttk.Treeview(
            entities_tree_frame, columns=("ID", "Start", "End", "Text", "Tag"),
            displaycolumns=("Start", "End", "Text", "Tag"), show="headings",
            yscrollcommand=scrollbar_entities_y.set, selectmode='extended'
        )
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
        self.relations_tree = ttk.Treeview(
            relations_tree_frame, columns=("ID", "Head", "Type", "Tail"),
            displaycolumns=("Head", "Type", "Tail"), show="headings",
            yscrollcommand=scrollbar_relations_y.set, selectmode='browse'
        )
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
        if col in ["Start", "End"] and tree == self.entities_tree:
            data = []
            for item in tree.get_children(""):
                pos_str = tree.set(item, col)
                try:
                    line, char = map(int, pos_str.split('.'))
                    data.append(((line, char), item))
                except ValueError:
                    data.append(((0, 0), item))
        else:
            data = [(tree.set(item, col).lower(), item) for item in tree.get_children("")]
        selection = tree.selection()
        data.sort(reverse=reverse)
        for index, (val, item) in enumerate(data):
            tree.move(item, "", index)
        valid_selection = [s for s in selection if tree.exists(s)]
        if valid_selection:
            tree.selection_set(valid_selection)
            if tree.exists(valid_selection[0]):
                tree.see(valid_selection[0])
        else:
            if tree == self.entities_tree:
                self.selected_entity_ids_for_relation = []
            self._update_button_states()

        for column_id in tree["displaycolumns"] if tree["displaycolumns"] != "#all" else tree["columns"]:
            try:
                current_text = tree.heading(column_id, 'text')
                base_text = current_text.replace(" ▲", "").replace(" ▼", "")
                tree.heading(column_id, text=base_text)
            except tk.TclError: pass
        indicator = "▼" if reverse else "▲"
        try:
            current_text = tree.heading(col, 'text')
            base_text = current_text.replace(" ▲", "").replace(" ▼", "")
            tree.heading(col, text=f"{base_text} {indicator}",
                         command=lambda c=col: self._treeview_sort_column(tree, c, not reverse))
        except tk.TclError: pass

    def _treeview_key_navigate(self, tree, event):
        if not event.char or not event.char.isprintable() or len(event.char) != 1:
            return
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
        """
        Handles creating annotations on drag-release and removing them on a simple click.
        """
        if not self.current_file_path: return

        CLICK_TIME_THRESHOLD = 0.5
        CLICK_MOVE_THRESHOLD = 10

        time_diff = time.time() - self._click_time
        move_diff = abs(event.x - self._click_pos[0]) + abs(event.y - self._click_pos[1])

        # A drag-selection was made
        try:
            sel_start = self.text_area.index(tk.SEL_FIRST)
            sel_end = self.text_area.index(tk.SEL_LAST)
            if sel_start != sel_end:
                self.annotate_selection()
                return # Action is complete
        except tk.TclError:
            pass # No drag selection, proceed to check for a click

        # A quick click was made (for removal ONLY)
        if time_diff < CLICK_TIME_THRESHOLD and move_diff < CLICK_MOVE_THRESHOLD:
            # Check if this click was part of a double-click action. If so, ignore it.
            if self._just_double_clicked:
                self._just_double_clicked = False # Reset the flag for the next action
                return
            original_state = self.text_area.cget('state')
            self.text_area.config(state=tk.NORMAL)
            try:
                click_index_str = self.text_area.index(f"@{event.x},{event.y}")
                click_pos = tuple(map(int, click_index_str.split('.')))

                clicked_entity_dict = None
                entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
                for entity in reversed(entities):
                    start_pos = (entity.get('start_line'), entity.get('start_char'))
                    end_pos = (entity.get('end_line'), entity.get('end_char'))
                    if start_pos <= click_pos < end_pos:
                        clicked_entity_dict = entity
                        break

                if clicked_entity_dict:
                    self._remove_entity_instance(clicked_entity_dict)

            except (tk.TclError, ValueError):
                pass # Ignore errors from clicking outside text
            finally:
                if self.text_area.winfo_exists():
                    self.text_area.config(state=original_state)

    def _on_double_click(self, event):
        """Selects and annotates the word under the cursor on double-click."""
        self._just_double_clicked = True
        if not self.current_file_path: return "break"

        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL)
        try:
            click_index_str = self.text_area.index(f"@{event.x},{event.y}")

            # Check if the click was inside an existing annotation to prevent re-annotating
            click_pos = tuple(map(int, click_index_str.split('.')))
            entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
            for entity in entities:
                start_pos = (entity.get('start_line'), entity.get('start_char'))
                end_pos = (entity.get('end_line'), entity.get('end_char'))
                if start_pos <= click_pos < end_pos:
                    return "break" # It's on an existing annotation, do nothing

            # If not on an existing annotation, select and annotate the word
            word_start = self.text_area.index(f"{click_index_str} wordstart")
            word_end = self.text_area.index(f"{click_index_str} wordend")
            if word_start != word_end:
                self.text_area.tag_remove(tk.SEL, "1.0", tk.END)
                self.text_area.tag_add(tk.SEL, word_start, word_end)
                self.annotate_selection()
        except (tk.TclError, ValueError):
            pass # Ignore clicks outside of text content
        finally:
            if self.text_area.winfo_exists():
                self.text_area.config(state=original_state)

        return "break" # Prevent default double-click actions (like selecting the line)

    def _remove_entity_instance(self, entity_to_remove):
        if not self.current_file_path or self.current_file_path not in self.annotations: return

        file_data = self.annotations[self.current_file_path]
        entities_list = file_data.get("entities", [])
        relations_list = file_data.get("relations", [])

        try:
            entity_index_to_remove = entities_list.index(entity_to_remove)
        except ValueError:
            messagebox.showerror("Error", "Could not find the clicked entity instance to remove.", parent=self.root)
            return

        entity_id_being_removed = entities_list[entity_index_to_remove].get('id')
        entity_text = entities_list[entity_index_to_remove].get('text', '')[:30]
        entity_tag_being_removed = entities_list[entity_index_to_remove].get('tag', 'N/A')

        confirm = messagebox.askyesno("Confirm Removal",
                                     f"Remove annotation for '{entity_text}...' ({entity_tag_being_removed})?",
                                     parent=self.root)
        if not confirm:
            self.status_var.set("Removal cancelled.")
            return

        self.text_area.tag_remove("selection_highlight", "1.0", tk.END)
        del entities_list[entity_index_to_remove]

        id_still_exists = any(e.get('id') == entity_id_being_removed for e in entities_list)
        removed_relation_count = 0
        if not id_still_exists and relations_list:
            relations_original_count = len(relations_list)
            relations_remaining = [rel for rel in relations_list if
                                   rel.get('head_id') != entity_id_being_removed and
                                   rel.get('tail_id') != entity_id_being_removed]
            removed_relation_count = relations_original_count - len(relations_remaining)
            file_data["relations"] = relations_remaining

        self.update_entities_list()
        self.update_relations_list()
        self.apply_annotations_to_text()
        self._update_button_states()
        status_msg = f"Removed annotation for '{entity_text}...'"
        if removed_relation_count > 0:
            status_msg += f" and {removed_relation_count} associated relations."
        self.status_var.set(status_msg)

    def get_color_for_tag(self, tag):
        if tag not in self.tag_colors:
            try:
                if tag in self.entity_tags:
                    self.tag_colors[tag] = next(self.color_cycle)
                else:
                    return "#cccccc"
            except Exception:
                self.tag_colors[tag] = "#cccccc"
        return self.tag_colors.get(tag, "#cccccc")

    def _configure_text_tags(self):
        for tag in self.entity_tags:
            color = self.get_color_for_tag(tag)
            try:
                self.text_area.tag_configure(tag, background=color, underline=False)
            except tk.TclError as e:
                print(f"Warning: Could not configure text tag '{tag}': {e}")
        try:
            if "propagated_entity" not in self.text_area.tag_names():
                self.text_area.tag_configure("propagated_entity", underline=True)
        except tk.TclError as e:
            print(f"Warning: Could not configure text tag 'propagated_entity': {e}")

        self.text_area.tag_configure("selection_highlight", borderwidth=2, relief=tk.SOLID)

    def _configure_treeview_tags(self):
        try:
            self.entities_tree.tag_configure('merged', foreground='grey', font=('TkDefaultFont', 9, 'italic'))
        except tk.TclError as e:
            print(f"Warning: Could not configure Treeview tags: {e}")

    def _update_entity_tag_combobox(self):
        current_selection = self.selected_entity_tag.get()
        if not self.entity_tags:
            self.selected_entity_tag.set("")
            self.entity_tag_combobox.config(values=[], state=tk.DISABLED)
        else:
            self.entity_tag_combobox['values'] = self.entity_tags
            if current_selection not in self.entity_tags:
                self.selected_entity_tag.set(self.entity_tags[0])
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

        self.annotate_btn.config(state=tk.NORMAL if file_loaded and self.entity_tags else tk.DISABLED)
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
            if not messagebox.askyesno("Unsaved Changes", "You have unsaved changes.\nDiscard and load new directory?", parent=self.root):
                return
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

    def add_files_to_session(self):
        if not self.files_list:
            messagebox.showwarning("No Session Active", "Please open a directory or load a session first.", parent=self.root)
            return

        source_paths = filedialog.askopenfilenames(
            title="Select Text File(s) to Add",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")],
            parent=self.root
        )
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
                try:
                    shutil.copy2(source_path, dest_path)
                except Exception as e:
                    messagebox.showerror("Copy Error", f"Could not copy file '{basename}'.\n\nError: {e}", parent=self.root)
                    continue

            self.files_list.append(dest_path)
            added_count += 1

        if added_count > 0:
            current_selection_path = self.current_file_path
            self.files_list.sort(key=lambda p: os.path.basename(p).lower())
            self.files_listbox.delete(0, tk.END)
            for path in self.files_list:
                self.files_listbox.insert(tk.END, os.path.basename(path))

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
                self.text_area.insert(tk.END, f.read())

            file_data = self.annotations.setdefault(self.current_file_path, {"entities": [], "relations": []})
            self.update_entities_list()
            self.update_relations_list()
            self.apply_annotations_to_text()
            self.status_var.set(f"Loaded: {filename} ({index+1}/{len(self.files_list)})")
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
        """Saves the current entity tags and relation types to a JSON file."""
        save_path = filedialog.asksaveasfilename(
            title="Save Tag/Relation Schema",
            defaultextension=".json",
            filetypes=[("ANNIE Schema Files", "*.json"), ("All files", "*.*")],
            parent=self.root
        )
        if not save_path:
            return

        schema_data = {
            "entity_tags": self.entity_tags,
            "relation_types": self.relation_types
        }
        try:
            with open(save_path, 'w', encoding='utf-8') as f:
                json.dump(schema_data, f, indent=2)
            self.status_var.set(f"Schema saved to {os.path.basename(save_path)}")
        except Exception as e:
            messagebox.showerror("Save Error", f"Could not save schema file:\n{e}", parent=self.root)

    def load_schema(self):
        """Loads entity tags and relation types from a JSON file, replacing the current ones."""
        if self.annotations and not messagebox.askyesno("Confirm Load",
            "Loading a new schema will replace your current tags. This may affect existing annotations if the tags don't match.\n\nContinue?"):
            return

        load_path = filedialog.askopenfilename(
            title="Load Tag/Relation Schema",
            filetypes=[("ANNIE Schema Files", "*.json"), ("All files", "*.*")],
            parent=self.root
        )
        if not load_path:
            return

        try:
            with open(load_path, 'r', encoding='utf-8') as f:
                schema_data = json.load(f)

            if "entity_tags" not in schema_data or "relation_types" not in schema_data:
                raise ValueError("File is not a valid schema file.")

            self.entity_tags = schema_data["entity_tags"]
            self.relation_types = schema_data["relation_types"]

            # Refresh the entire UI to reflect the new schema
            self._update_entity_tag_combobox()
            self._update_relation_type_combobox()
            self._ensure_default_colors() # Assign colors to any new tags
            self._configure_text_tags()

            # If a file is open, refresh its views
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
            tags_to_clear = set(self.entity_tags) | {"propagated_entity", "selection_highlight", tk.SEL}
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

    def save_annotations(self):
        if not self.annotations or all(not data.get('entities') and not data.get('relations') for data in self.annotations.values()):
            messagebox.showinfo("Info", "There are no annotations to save.", parent=self.root)
            return

        initial_dir = os.path.dirname(self.files_list[0]) if self.files_list else ""
        save_path = filedialog.asksaveasfilename(
            initialdir=initial_dir, initialfile="annotations.json", defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")], parent=self.root
        )
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
                "relations": sorted(data.get("relations", []), key=lambda r: (r.get('type', ''), r.get('head_id','')))
            }

        try:
            with open(save_path, 'w', encoding='utf-8') as f:
                json.dump(serializable_annotations, f, indent=2, ensure_ascii=False)
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
                filetypes=[("ANNIE Session files", "*.json"), ("All files", "*.*")], parent=self.root
            )
        if not save_path:
            self.status_var.set("Save session cancelled.")
            return

        session_data = {
            "version": SESSION_FILE_VERSION,
            "files_list": self.files_list,
            "current_file_index": self.current_file_index,
            "entity_tags": self.entity_tags,
            "relation_types": self.relation_types,
            "tag_colors": self.tag_colors,
            "annotations": self.annotations,
            "extend_to_word": self.extend_to_word.get(),
            "allow_multilabel_overlap": self.allow_multilabel_overlap.get(),
            "last_used_ai_models": self.last_used_ai_models,
            "current_ai_models": self.current_ai_models
        }
        try:
            with open(save_path, 'w', encoding='utf-8') as f:
                json.dump(session_data, f, indent=2, ensure_ascii=False)

            self.session_save_path = save_path
            self.status_var.set(f"Session saved to '{os.path.basename(save_path)}'")

            # Get the base directory name reliably from the file list
            base_dir_name = os.path.basename(os.path.dirname(self.files_list[0]))
            self.root.title(f"ANNIE - {base_dir_name} [{os.path.basename(save_path)}]")

        except Exception as e:
            messagebox.showerror("Save Session Error", f"Could not write session file:\n{e}", parent=self.root)

    def load_session(self):
        if self._has_unsaved_changes():
            response = messagebox.askyesnocancel("Unsaved Changes", "You have unsaved changes.\nDiscard and load session?", parent=self.root)
            if response is None:
                return
            if response:
                self.save_session()
                if not self.session_save_path:
                    return

        load_path = filedialog.askopenfilename(
            filetypes=[("ANNIE Session files", "*.json"), ("All files", "*.*")], parent=self.root
        )
        if not load_path: return

        try:
            with open(load_path, 'r', encoding='utf-8') as f:
                session_data = json.load(f)
        except Exception as e:
            messagebox.showerror("Load Session Error", f"Could not read session file:\n{e}", parent=self.root)
            return

        required_keys = ["files_list", "annotations", "entity_tags", "relation_types"]
        if not all(key in session_data for key in required_keys):
            messagebox.showerror("Load Session Error", "Session file is missing required data.", parent=self.root)
            return

        missing_files = [fp for fp in session_data["files_list"] if not os.path.isfile(fp)]
        if missing_files:
            msg = "Some text files could not be found:\n- " + "\n- ".join(os.path.basename(p) for p in missing_files[:5])
            if not messagebox.askyesno("Missing Files", f"{msg}\n\nContinue loading session?", parent=self.root):
                return

        self._reset_state()
        try:
            self.files_list = session_data["files_list"]
            self.annotations = session_data["annotations"]
            self.entity_tags = session_data["entity_tags"]
            self.relation_types = session_data["relation_types"]
            self.tag_colors = session_data.get("tag_colors", {})
            self.extend_to_word.set(session_data.get("extend_to_word", False))
            self.allow_multilabel_overlap.set(session_data.get("allow_multilabel_overlap", True))
            self.session_save_path = load_path
            self.last_used_ai_models = session_data.get("last_used_ai_models", [])
            self.current_ai_models = session_data.get("current_ai_models", [])

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
            if self.files_list and 0 <= idx_to_load < len(self.files_list):
                 self.load_file(idx_to_load)
            else:
                self.status_var.set("Session loaded. No files to display.")

            base_dir_name = os.path.basename(os.path.dirname(self.files_list[0])) if self.files_list else "Session"
            self.root.title(f"ANNIE - {base_dir_name} [{os.path.basename(load_path)}]")
        except Exception as e:
            messagebox.showerror("Load Session Error", f"Error applying session data:\n{e}", parent=self.root)
            self._reset_state()
        finally:
            self._update_button_states()

    def _has_unsaved_changes(self):
        return bool(self.files_list)

    def _on_closing(self):
        if self._has_unsaved_changes():
            response = messagebox.askyesnocancel("Exit Confirmation", "You have an active session.\nSave before exiting?", parent=self.root)
            if response is True:
                self.save_session()
                if self.session_save_path: self.root.quit()
            elif response is False:
                self.root.quit()
        else:
            self.root.quit()

    def _tkinter_index_to_char_offset(self, text, line, char):
        """Converts a Tkinter 'line.char' index to an absolute character offset."""
        lines = text.split('\n')
        # Sum the length of all preceding lines plus 1 for each newline character
        offset = sum(len(l) + 1 for l in lines[:line - 1])
        offset += char
        return offset

    # Import/Export Methods
    def export_annotations(self):
        """Exports annotations for the entire session in a standard ML training format."""
        if not self.annotations or all(not data.get('entities') for data in self.annotations.values()):
            messagebox.showinfo("Info", "There are no annotations to export.", parent=self.root)
            return

        save_path = filedialog.asksaveasfilename(
            title="Export Annotations for Training",
            initialdir=os.path.dirname(self.files_list[0]) if self.files_list else "",
            filetypes=[
                ("CoNLL Files", "*.conll"),
                ("spaCy JSONL Files", "*.jsonl"),
                ("All files", "*.*")
            ],
            parent=self.root
        )

        if not save_path:
            self.status_var.set("Export cancelled.")
            return

        try:
            # Determine which export function to call based on the chosen file extension
            if save_path.lower().endswith(".conll"):
                self._export_as_conll(save_path)
            elif save_path.lower().endswith(".jsonl"):
                self._export_as_spacy_jsonl(save_path)
            else:
                messagebox.showwarning("Unknown Format", "File was saved with an unknown extension. Please use '.conll' or '.jsonl'.", parent=self.root)
                return

            messagebox.showinfo("Success", f"Annotations successfully exported to:\n{os.path.basename(save_path)}", parent=self.root)
            self.status_var.set(f"Exported annotations to {os.path.basename(save_path)}")
        except Exception as e:
            messagebox.showerror("Export Error", f"An error occurred during export:\n{e}", parent=self.root)
            traceback.print_exc()

    def _export_as_spacy_jsonl(self, save_path):
        """Exports all documents to a single spaCy v3 JSONL file."""
        with open(save_path, 'w', encoding='utf-8') as f:
            for file_path, data in self.annotations.items():
                if not data.get("entities"): continue

                try:
                    with open(file_path, 'r', encoding='utf-8') as text_file:
                        content = text_file.read()
                except Exception:
                    print(f"Warning: Could not read file {file_path} for export. Skipping.")
                    continue

                entities = []
                for ann in data['entities']:
                    # Use the new helper to get absolute character positions from the actual file content
                    start_char = self._tkinter_index_to_char_offset(content, ann['start_line'], ann['start_char'])
                    end_char = self._tkinter_index_to_char_offset(content, ann['end_line'], ann['end_char'])
                    entities.append([start_char, end_char, ann['tag']])

                spacy_doc = {"text": content, "entities": entities}
                f.write(json.dumps(spacy_doc, ensure_ascii=False) + '\n')

    def _export_as_conll(self, save_path):
        """Exports all documents to a single CoNLL-2003 formatted file."""
        with open(save_path, 'w', encoding='utf-8') as f:
            for file_path, data in self.annotations.items():
                if not data.get("entities"): continue

                try:
                    with open(file_path, 'r', encoding='utf-8') as text_file:
                        content = text_file.read()
                except Exception:
                    print(f"Warning: Could not read file {file_path} for export. Skipping.")
                    continue

                # Simple regex tokenizer: finds sequences of word characters or single non-word/non-space characters
                tokens = [(m.group(0), m.start()) for m in re.finditer(r'\w+|[^\w\s]', content)]
                tags = ["O"] * len(tokens)

                sorted_entities = sorted(data['entities'], key=lambda x: (x['start_line'], x['start_char']))

                for entity in sorted_entities:
                    # Use the new helper to get absolute character positions from the actual file content
                    start_char_abs = self._tkinter_index_to_char_offset(content, entity['start_line'], entity['start_char'])
                    end_char_abs = self._tkinter_index_to_char_offset(content, entity['end_line'], entity['end_char'])

                    is_first_token = True
                    for i, (token_text, token_start) in enumerate(tokens):
                        token_end = token_start + len(token_text)
                        # Check if the token is within the entity span
                        if token_start >= start_char_abs and token_end <= end_char_abs:
                            if is_first_token:
                                tags[i] = f"B-{entity['tag']}"
                                is_first_token = False
                            else:
                                tags[i] = f"I-{entity['tag']}"

                # Write tokens and tags to file
                for i, (token_text, _) in enumerate(tokens):
                    f.write(f"{token_text} {tags[i]}\n")

                # Add a blank line to separate documents
                f.write("\n")

    def _ask_for_save_directory(self, initial_dir):
        """Creates a custom dialog to select or create a directory."""
        dialog = tk.Toplevel(self.root)
        dialog.title("Select Save Directory")
        dialog.geometry("500x150")
        dialog.transient(self.root)
        dialog.grab_set()

        result = {"path": ""}

        tk.Label(dialog, text="Choose a directory to save the imported files into.\nYou can browse for one or type a path to a new folder.").pack(pady=10)

        entry_frame = tk.Frame(dialog)
        entry_frame.pack(fill=tk.X, padx=10)

        path_var = tk.StringVar(value=initial_dir)
        entry = tk.Entry(entry_frame, textvariable=path_var)
        entry.pack(side=tk.LEFT, fill=tk.X, expand=True)

        def browse():
            dir_path = filedialog.askdirectory(initialdir=path_var.get(), parent=dialog)
            if dir_path:
                path_var.set(dir_path)

        browse_btn = tk.Button(entry_frame, text="Browse...", command=browse)
        browse_btn.pack(side=tk.LEFT, padx=(5,0))

        btn_frame = tk.Frame(dialog)
        btn_frame.pack(pady=10)

        def on_ok():
            result["path"] = path_var.get()
            dialog.destroy()

        def on_cancel():
            result["path"] = ""
            dialog.destroy()

        ok_btn = tk.Button(btn_frame, text="OK", width=10, command=on_ok)
        ok_btn.pack(side=tk.LEFT, padx=5)
        cancel_btn = tk.Button(btn_frame, text="Cancel", width=10, command=on_cancel)
        cancel_btn.pack(side=tk.LEFT, padx=5)

        self.root.wait_window(dialog)
        return result["path"]

    def import_annotations(self):
        """Imports annotations from CoNLL or spaCy JSONL files, creating new documents."""
        from tkinter import simpledialog

        import_path = filedialog.askopenfilename(
            title="Select Annotation File to Import",
            filetypes=[("All Supported Formats", "*.conll *.jsonl"), ("CoNLL Files", "*.conll"), ("JSONL Files", "*.jsonl")],
            parent=self.root
        )
        if not import_path: return

        try:
            # Parse the file based on its type
            parsed_docs, found_tags = [], set()
            if import_path.lower().endswith(".conll"):
                parsed_docs, found_tags = self._parse_conll_into_documents(import_path)
            elif import_path.lower().endswith(".jsonl"):
                parsed_docs, found_tags = self._parse_jsonl_into_documents(import_path)
            else:
                messagebox.showwarning("Unsupported Format", "Please select a .conll or .jsonl file.")
                return

            if not parsed_docs:
                messagebox.showinfo("Info", "No valid documents found in the import file.", parent=self.root)
                return

            # Handle new tags
            new_tags = found_tags - set(self.entity_tags)
            if new_tags:
                if messagebox.askyesno("New Tags Found", f"Found new tags: {', '.join(new_tags)}.\n\nAdd them to the session?"):
                    self.entity_tags.extend(list(new_tags))
                    self._update_entity_tag_combobox()
                    self._configure_text_tags()
                else:
                    approved_tags = set(self.entity_tags)
                    for doc in parsed_docs:
                        doc['annotations'] = [ann for ann in doc['annotations'] if ann['tag'] in approved_tags]

            # Get save location
            save_dir = self._ask_for_save_directory(os.path.dirname(import_path))
            if not save_dir:
                self.status_var.set("Import cancelled.")
                return
            os.makedirs(save_dir, exist_ok=True)

            # Save files and update UI
            if not self.files_list and parsed_docs: self._reset_state()

            base_name_for_docs = os.path.basename(os.path.splitext(import_path)[0])
            new_file_paths = []
            for i, doc in enumerate(parsed_docs):
                save_path = os.path.join(save_dir, f"{base_name_for_docs}_{i+1}.txt")
                with open(save_path, 'w', encoding='utf-8') as f:
                    f.write(doc['text'])

                self.files_list.append(save_path)
                new_file_paths.append(save_path)

                final_annotations = []
                for ann in doc['annotations']:
                    start_pos = self._char_offset_to_tkinter_index(doc['text'], ann['start'])
                    end_pos = self._char_offset_to_tkinter_index(doc['text'], ann['end'])
                    start_line, start_char = map(int, start_pos.split('.'))
                    end_line, end_char = map(int, end_pos.split('.'))
                    text = doc['text'][ann['start']:ann['end']]

                    final_annotations.append({'id': uuid.uuid4().hex, 'start_line': start_line, 'start_char': start_char,
                                              'end_line': end_line, 'end_char': end_char, 'text': text, 'tag': ann['tag']})
                self.annotations[save_path] = {"entities": final_annotations, "relations": []}

            self.files_listbox.delete(0, tk.END)
            for path in self.files_list:
                self.files_listbox.insert(tk.END, os.path.basename(path))

            self.load_file(len(self.files_list) - len(new_file_paths))
            self.status_var.set(f"Successfully imported {len(parsed_docs)} documents.")

        except Exception as e:
            messagebox.showerror("Import Error", f"An error occurred during import:\n{e}", parent=self.root)
            traceback.print_exc()

    def _parse_conll_into_documents(self, file_path):
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        doc_chunks = re.split(r'\n\s*\n|-DOCSTART-.*\n', content)
        documents = []
        all_tags = set()

        for chunk in doc_chunks:
            if not chunk.strip(): continue

            doc_lines = chunk.strip().splitlines()
            text, annotations, tags = self._process_conll_chunk(doc_lines)
            if text.strip():
                documents.append({'text': text, 'annotations': annotations})
                all_tags.update(tags)

        return documents, all_tags

    def _parse_jsonl_into_documents(self, file_path):
        """
        Parses a JSONL file (from Prodigy or spaCy) into a list of document objects.
        """
        documents = []
        all_tags = set()
        with open(file_path, 'r', encoding='utf-8') as f:
            # The file can have multiple JSON objects on one line, so we need to handle that
            content = f.read().strip()
            # Split by '}{' to handle concatenated JSON and re-add the braces
            json_objects_str = content.replace('}{', '}\n{').splitlines()

            for line in json_objects_str:
                if not line.strip(): continue

                data = json.loads(line)
                text = data.get("text")

                # Look for "spans" instead of "entities" ---
                spans = data.get("spans", [])

                if text:
                    annotations = []
                    for span in spans:
                        # Use the correct keys from the span dictionary: "start", "end", "label"
                        start = span.get("start")
                        end = span.get("end")
                        tag = span.get("label")

                        if start is not None and end is not None and tag is not None:
                            annotations.append({'start': start, 'end': end, 'tag': tag})
                            all_tags.add(tag)

                    documents.append({'text': text, 'annotations': annotations})

        return documents, all_tags


    def _process_conll_chunk(self, lines):
        """Helper to process a list of CoNLL lines into text and annotations."""
        reconstructed_text = ""
        annotations = []
        found_tags = set()
        current_char = 0
        current_entity = None

        for line in lines:
            line = line.strip()
            if not line:
                if reconstructed_text and not reconstructed_text.endswith(('\n', ' ')):
                    reconstructed_text += "\n" # Treat blank lines within a doc as sentence breaks
                    current_char += 1
                if current_entity:
                    annotations.append(current_entity)
                    current_entity = None
                continue

            parts = line.split()
            if len(parts) < 2: continue
            token, tag = parts[0], parts[-1]

            # Smartly add space before the next token, but not after a newline
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
            else: # O tag
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
            if self._spans_overlap_numeric(start_l, start_c, end_l, end_c, ann['start_line'], ann['start_char'], ann['end_line'], ann['end_char']):
                return True
        return False

    def annotate_selection(self):
        if not self.current_file_path or not self.entity_tags: return

        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL)
        try:
            start_pos = self.text_area.index(tk.SEL_FIRST)
            end_pos = self.text_area.index(tk.SEL_LAST)
            if start_pos == end_pos: return

            #  first, then trim.
            # Snap the initial user selection to the nearest word boundaries.
            snapped_start_pos = self.text_area.index(f"{start_pos} wordstart")
            snapped_end_pos = self.text_area.index(f"{self.text_area.index(f'{end_pos}-1c')} wordend")

            if self.text_area.compare(snapped_start_pos, ">=", snapped_end_pos): return

            # Get the text from this snapped selection.
            snapped_text = self.text_area.get(snapped_start_pos, snapped_end_pos)

            # Trim any leading/trailing whitespace from the text and adjust positions.
            leading_spaces = len(snapped_text) - len(snapped_text.lstrip())
            trailing_spaces = len(snapped_text) - len(snapped_text.rstrip())

            final_text = snapped_text.strip()
            if not final_text: return # Selection was only whitespace

            final_start_pos = self.text_area.index(f"{snapped_start_pos}+{leading_spaces}c")
            final_end_pos = self.text_area.index(f"{snapped_end_pos}-{trailing_spaces}c")

            start_line, start_char = map(int, final_start_pos.split('.'))
            end_line, end_char = map(int, final_end_pos.split('.'))
            tag = self.selected_entity_tag.get()
            if not tag: return

            entities_in_file = self.annotations.get(self.current_file_path, {}).get("entities", [])

            if not self.allow_multilabel_overlap.get():
                if self._is_overlapping_in_list(start_line, start_char, end_line, end_char, entities_in_file):
                    messagebox.showwarning("Overlap Detected", "Annotation overlaps with an existing one. Enable multi-label in Settings to allow this.", parent=self.root)
                    return
            else: # Check for absolute duplicates even if overlap is allowed
                for ann in entities_in_file:
                    if (ann['start_line'] == start_line and ann['start_char'] == start_char and
                        ann['end_line'] == end_line and ann['end_char'] == end_char and ann['tag'] == tag):
                        self.status_var.set("This exact annotation already exists.")
                        return

            entity_id = uuid.uuid4().hex
            annotation = {'id': entity_id, 'start_line': start_line, 'start_char': start_char,
                          'end_line': end_line, 'end_char': end_char, 'text': final_text, 'tag': tag}
            entities_in_file.append(annotation)

            self.text_area.tag_remove(tk.SEL, "1.0", tk.END)
            self.apply_annotations_to_text()
            self.update_entities_list()
            self.status_var.set(f"Annotated: '{final_text[:30].replace(os.linesep, ' ')}...' as {tag}")
            self._update_button_states()

        except tk.TclError:
            pass # No selection exists
        except Exception as e:
            messagebox.showerror("Annotation Error", f"An unexpected error occurred:\n{e}", parent=self.root)
            traceback.print_exc()
        finally:
            if self.text_area.winfo_exists() and original_state == tk.DISABLED:
                self.text_area.config(state=tk.DISABLED)

    def remove_entity_annotation(self, event=None):
        if self._is_deleting:
            return
        self._is_deleting = True
        try:
            selected_iids = self.entities_tree.selection()
            if not selected_iids:
                messagebox.showinfo("Info", "Select one or more entities to remove.", parent=self.root)
                return

            # Get the index of the first selected item BEFORE deleting to select the next item later
            all_iids_before = self.entities_tree.get_children()
            next_selection_index = 0
            if all_iids_before:
                try:
                    next_selection_index = all_iids_before.index(selected_iids[0])
                except ValueError:
                    pass

            if not messagebox.askyesno("Confirm Removal", f"Remove {len(selected_iids)} selected entity instance(s)?"):
                return

            # Find the data dictionaries corresponding to the selected row IDs
            entities_in_file = self.annotations.get(self.current_file_path, {}).get("entities", [])
            ids_to_remove, data_to_remove = set(), []
            for iid in selected_iids:
                try:
                    parts = iid.split('|')
                    if len(parts) < 6: continue
                    entity_id, start_pos, end_pos, tag = parts[1], parts[2], parts[3], parts[4]
                    for entity_dict in entities_in_file:
                        if (entity_dict['id'] == entity_id and
                            f"{entity_dict['start_line']}.{entity_dict['start_char']}" == start_pos and
                            entity_dict['tag'] == tag):
                            data_to_remove.append(entity_dict)
                            ids_to_remove.add(entity_id)
                            break
                except IndexError:
                    continue

            if not data_to_remove:
                messagebox.showerror("Error", "Could not retrieve data for selected entities.", parent=self.root)
                return

            # Perform the data deletion
            for item in data_to_remove:
                if item in entities_in_file:
                    entities_in_file.remove(item)

            # Handle orphaned relations
            relations = self.annotations[self.current_file_path].get("relations", [])
            if relations:
                remaining_ids = {e['id'] for e in entities_in_file}
                orphaned_ids = ids_to_remove - remaining_ids
                if orphaned_ids:
                    self.annotations[self.current_file_path]["relations"] = [
                        r for r in relations if r['head_id'] not in orphaned_ids and r['tail_id'] not in orphaned_ids
                    ]

            # Update all UI elements, passing the index-to-select as a hint
            self.apply_annotations_to_text()
            self.update_relations_list()
            self.update_entities_list(selection_hint=next_selection_index) # This now handles focus
            self.status_var.set(f"Removed {len(data_to_remove)} entity instances.")

        finally:
            self._is_deleting = False

    def merge_selected_entities(self):
        selected_tree_iids = self.entities_tree.selection()
        if len(selected_tree_iids) < 2:
            messagebox.showinfo("Info", "Select 2+ entity instances to merge.", parent=self.root)
            return

        entities_in_file = self.annotations.get(self.current_file_path, {}).get("entities", [])
        selected_entities_data = []

        for tree_iid in selected_tree_iids:
            try:
                parts = tree_iid.split('|')
                if len(parts) < 6: continue
                entity_id, start_pos_str, end_pos_str, tag = parts[1], parts[2], parts[3], parts[4]

                for entity_dict in entities_in_file:
                    if (entity_dict['id'] == entity_id and
                        f"{entity_dict['start_line']}.{entity_dict['start_char']}" == start_pos_str and
                        f"{entity_dict['end_line']}.{entity_dict['end_char']}" == end_pos_str and
                        entity_dict['tag'] == tag):
                        if entity_dict not in selected_entities_data:
                            selected_entities_data.append(entity_dict)
                        break
            except Exception as e:
                print(f"Warning: Could not get data for merge: {e}")

        if len(selected_entities_data) < 2:
            messagebox.showerror("Error", "Need at least two valid and distinct instances to merge.", parent=self.root)
            return

        selected_entities_data.sort(key=lambda e: (e['start_line'], e['start_char']))
        canonical_entity = selected_entities_data[0]
        canonical_id = canonical_entity['id']

        ids_to_change = {e['id'] for e in selected_entities_data if e['id'] != canonical_id}
        if not ids_to_change:
            messagebox.showinfo("Info", "Selected instances already share the same ID.", parent=self.root)
            return

        for entity in selected_entities_data:
            if entity['id'] in ids_to_change:
                entity['id'] = canonical_id

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
        self.status_var.set(f"Merged {len(selected_entities_data)} instances to ID {canonical_id[:8]}...")

    def _on_text_right_click(self, event):
        if not self.current_file_path: return
        try:
            click_index_str = self.text_area.index(f"@{event.x},{event.y}")
            click_pos = tuple(map(int, click_index_str.split('.')))
        except (tk.TclError, ValueError): return

        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        clicked_entity = None
        for entity in reversed(entities):
            if (entity['start_line'], entity['start_char']) <= click_pos < (entity['end_line'], entity['end_char']):
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
        entity_to_demerge['id'] = uuid.uuid4().hex
        self.update_entities_list()
        self.apply_annotations_to_text()
        self.status_var.set(f"Demerged instance. New ID: {entity_to_demerge['id'][:8]}...")

    def apply_annotations_to_text(self):
        if not self.current_file_path: return
        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL)
        try:
            tags_to_clear = set(self.entity_tags) | {"propagated_entity"}
            for tag in tags_to_clear:
                self.text_area.tag_remove(tag, "1.0", tk.END)

            entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
            sorted_entities = sorted(entities, key=lambda a: (a['start_line'], a['start_char'], -a['end_line'], -a['end_char']))

            for ann in sorted_entities:
                try:
                    start_pos = f"{ann['start_line']}.{ann['start_char']}"
                    end_pos = f"{ann['end_line']}.{ann['end_char']}"
                    tag = ann['tag']
                    if tag in self.entity_tags:
                        self.text_area.tag_raise(tag)
                        self.text_area.tag_add(tag, start_pos, end_pos)
                        if ann.get('propagated'):
                            self.text_area.tag_add("propagated_entity", start_pos, end_pos)
                except Exception as e:
                    print(f"Warning: Could not apply highlight for annotation {ann.get('id')}: {e}")
        finally:
            if self.text_area.winfo_exists():
                self.text_area.config(state=original_state)

    def update_entities_list(self, selection_hint=None):
        """
        Rebuilds the entire entity list and intelligently restores selection and focus.
        'selection_hint' can be an index (for after deletion) or a set of data tuples
        (for after re-labeling).
        """
        # Clear and rebuild the list
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

        # Intelligently restore selection and focus
        new_iids_to_select = []
        all_iids_after = self.entities_tree.get_children()

        if isinstance(selection_hint, int) and all_iids_after: # Del logic
            new_index = min(selection_hint, len(all_iids_after) - 1)
            new_iids_to_select.append(all_iids_after[new_index])

        elif isinstance(selection_hint, set): # Labelling logic
            for iid in all_iids_after:
                try:
                    parts = iid.split('|')
                    key = (parts[1], parts[2], parts[3], parts[4]) # (id, start, end, tag)
                    if key in selection_hint:
                        new_iids_to_select.append(iid)
                except IndexError: continue

        if new_iids_to_select:
            self.entities_tree.selection_set(new_iids_to_select)

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
            if self.text_area.winfo_exists():
                self.text_area.config(state=original_state)
        self._update_button_states()

    def add_relation(self):
        if len(self.selected_entity_ids_for_relation) != 2:
            messagebox.showerror("Selection Error", "Select exactly TWO unique entities from the list.", parent=self.root)
            return

        head_id, tail_id = self.selected_entity_ids_for_relation
        relation_type = self.selected_relation_type.get()
        if not relation_type: return

        relations_list = self.annotations.setdefault(self.current_file_path, {}).setdefault("relations", [])
        if any(r['head_id'] == head_id and r['tail_id'] == tail_id and r['type'] == relation_type for r in relations_list):
            messagebox.showwarning("Duplicate", "This exact relation already exists.", parent=self.root)
            return

        new_relation = {"id": uuid.uuid4().hex, "type": relation_type, "head_id": head_id, "tail_id": tail_id}
        relations_list.append(new_relation)
        self.update_relations_list()
        self.status_var.set(f"Added Relation: {relation_type}")

    def flip_selected_relation(self):
        selected_iids = self.relations_tree.selection()
        if not selected_iids: return

        relation_id = selected_iids[0]
        relations = self.annotations[self.current_file_path].get("relations", [])
        if not relations: return

        for rel in relations:
            if rel['id'] == relation_id:
                rel['head_id'], rel['tail_id'] = rel['tail_id'], rel['head_id']
                self.update_relations_list()
                self.status_var.set("Relation flipped.")
                break

    def remove_relation_annotation(self, event=None):
        selected_iids = self.relations_tree.selection()
        if not selected_iids: return
        relation_id = selected_iids[0]
        relations = self.annotations[self.current_file_path].get("relations", [])
        if not relations: return

        self.annotations[self.current_file_path]["relations"] = [r for r in relations if r['id'] != relation_id]
        self.update_relations_list()
        self.status_var.set("Relation removed.")

    def update_relations_list(self):
        selected_iids = self.relations_tree.selection()
        try: self.relations_tree.delete(*self.relations_tree.get_children())
        except Exception: pass
        if not self.current_file_path: return

        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        relations = self.annotations.get(self.current_file_path, {}).get("relations", [])
        if not relations: return

        entity_display_map = { e['id']: e['text'][:25] + ('...' if len(e['text']) > 25 else '') for e in entities }

        for rel in sorted(relations, key=lambda r: r['type']):
            head_text = entity_display_map.get(rel['head_id'], f"ID: {rel['head_id'][:6]}...")
            tail_text = entity_display_map.get(rel['tail_id'], f"ID: {rel['tail_id'][:6]}...")
            values = (rel['id'], head_text, rel['type'], tail_text)
            self.relations_tree.insert("", tk.END, iid=rel['id'], values=values)

        if selected_iids:
            self.relations_tree.selection_set(selected_iids)

        self._update_button_states()

    def on_relation_select(self, event=None):
        self._update_button_states()

    def propagate_annotations(self):
        if not self.current_file_path: return
        source_entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        if not source_entities:
            messagebox.showinfo("Info", "No entities in current file to propagate.", parent=self.root)
            return

        text_to_tag = {ann['text'].strip(): ann['tag'] for ann in sorted(source_entities, key=lambda a: (a['start_line'], a['start_char'])) if ann['text'].strip()}
        if not text_to_tag: return

        if not messagebox.askyesno("Confirm Propagation", f"Propagate {len(text_to_tag)} unique entities across all files?", parent=self.root):
            return

        self._perform_propagation(text_to_tag, "Current File Propagation")

    def load_and_propagate_from_dictionary(self):
        if not self.files_list: return
        dict_path = filedialog.askopenfilename(title="Select Dictionary File", filetypes=[("Text files", "*.txt"), ("All files", "*.*")])
        if not dict_path: return

        dictionary_mapping = {}
        try:
            with open(dict_path, 'r', encoding='utf-8') as f:
                for line in f:
                    if line.strip() and not line.startswith('#'):
                        parts = line.strip().split(None, 1)
                        if len(parts) == 2 and parts[1] in self.entity_tags:
                            dictionary_mapping[parts[0]] = parts[1]
        except Exception as e:
            messagebox.showerror("Dict Read Error", f"Failed to read dictionary:\n{e}", parent=self.root)
            return

        if not dictionary_mapping:
            messagebox.showinfo("Info", "No valid entries found in dictionary.", parent=self.root)
            return

        if not messagebox.askyesno("Confirm Propagation", f"Propagate {len(dictionary_mapping)} entities from dictionary?", parent=self.root):
            return

        self._perform_propagation(dictionary_mapping, "Dictionary Propagation")

    def _perform_propagation(self, text_to_tag_map, source_description):
        propagated_count, affected_files = 0, set()
        allow_overlap = self.allow_multilabel_overlap.get()

        self.status_var.set(f"Starting {source_description}..."); self.root.update()
        sorted_texts = sorted(text_to_tag_map.keys(), key=len, reverse=True)

        for file_path in self.files_list:
            try:
                with open(file_path, 'r', encoding='utf-8') as f: content = f.read()
            except Exception: continue

            target_entities = self.annotations.setdefault(file_path, {"entities": [], "relations": []})['entities']

            # Create a set of existing annotations for quick, accurate checking
            existing_spans_and_tags = {
                (ann['start_line'], ann['start_char'], ann['end_line'], ann['end_char'], ann['tag'])
                for ann in target_entities
            }

            for text_to_find in sorted_texts:
                tag = text_to_tag_map[text_to_find]
                # Use word boundaries (\b) to ensure we match whole words
                for match in re.finditer(r'\b' + re.escape(text_to_find) + r'\b', content):
                    start_char_offset, end_char_offset = match.span()

                    start_pos = self._char_offset_to_tkinter_index(content, start_char_offset)
                    end_pos = self._char_offset_to_tkinter_index(content, end_char_offset)
                    start_l, start_c = map(int, start_pos.split('.'))
                    end_l, end_c = map(int, end_pos.split('.'))

                    # Check against our set of existing annotations
                    current_span_and_tag = (start_l, start_c, end_l, end_c, tag)
                    if current_span_and_tag in existing_spans_and_tags:
                        continue

                    if not allow_overlap and self._is_overlapping_in_list(start_l, start_c, end_l, end_c, target_entities):
                        continue

                    new_ann = {'id': uuid.uuid4().hex, 'start_line': start_l, 'start_char': start_c,
                               'end_line': end_l, 'end_char': end_c, 'text': text_to_find,
                               'tag': tag, 'propagated': True}

                    target_entities.append(new_ann)
                    # Add the new annotation to our check-set to avoid duplicating it within the same run
                    existing_spans_and_tags.add(current_span_and_tag)
                    propagated_count += 1
                    affected_files.add(file_path)

        if self.current_file_path in affected_files:
            self.update_entities_list()
            self.apply_annotations_to_text()

        self._update_button_states()
        self.status_var.set(f"{source_description} complete. Added {propagated_count} entities across {len(affected_files)} files.")

    def manage_entity_tags(self):
        self._manage_items("Entity Tags", self.entity_tags, self._update_entity_tag_combobox)

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
                if hotkey_num == 0: hotkey_num = 0 # Map 10th item to 0
                display_text = f"{hotkey_num}: {item}"

            listbox.insert(tk.END, display_text)

            if item_type_name == "Entity Tags":
                try:
                    listbox.itemconfig(index, {'bg': self.get_color_for_tag(item)})
                except tk.TclError: pass

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
                    # Re-sort and re-display
                    updated_items = list(listbox.get(0, tk.END))
                    listbox.delete(0, tk.END)
                    for i_val in sorted(updated_items, key=str.lower):
                        listbox.insert(tk.END, i_val)
                    item_var.set("")
                else:
                    messagebox.showwarning("Duplicate", f"'{item}' already exists.", parent=window)
            item_entry.focus_set()

        item_entry.bind("<Return>", lambda event: add_item())
        add_btn = tk.Button(controls_frame, text="Add", width=7, command=add_item)
        add_btn.grid(row=0, column=1, padx=5)

        def remove_item():
            indices = listbox.curselection()
            if indices:
                for index in sorted(indices, reverse=True):
                    listbox.delete(index)
            else:
                messagebox.showwarning("No Selection", "Select item(s) to remove.", parent=window)

        remove_btn = tk.Button(controls_frame, text="Remove", width=7, command=remove_item)
        remove_btn.grid(row=0, column=2)
        button_frame = tk.Frame(window); button_frame.pack(fill=tk.X, padx=10, pady=(5, 10))

        def save_changes():
            new_items_raw = list(listbox.get(0, tk.END))
            if item_type_name == "Entity Tags":
                new_items = [re.sub(r"^\d:\s*", "", item) for item in new_items_raw]
            else:
                new_items = new_items_raw

            if set(new_items) != set(current_items_list):
                current_items_list[:] = new_items
                update_combobox_func()
                if item_type_name == "Entity Tags":
                    self._configure_text_tags()
                    self.apply_annotations_to_text()
                    self.update_entities_list()
                elif item_type_name == "Relation Types":
                    self.update_relations_list()
            window.destroy()

        save_btn = tk.Button(button_frame, text="Save Changes", width=12, command=save_changes)
        save_btn.pack(side=tk.RIGHT, padx=5)
        cancel_btn = tk.Button(button_frame, text="Cancel", width=12, command=window.destroy)
        cancel_btn.pack(side=tk.RIGHT)
        item_entry.focus_set()
        window.wait_window()

    def manage_entity_tags(self):
        self._manage_items("Entity Tags", self.entity_tags, self._update_entity_tag_combobox)

    def manage_relation_types(self):
        self._manage_items("Relation Types", self.relation_types, self._update_relation_type_combobox)


    # AI Pre-annotation Methods
    def _update_status_threadsafe(self, message):
        """Schedules a status bar update to make it thread-safe."""
        self.ai_status_queue.put(message)

    def _process_queue(self):
        """Processes messages from the queue in the main thread."""
        try:
            while True:
                message = self.ai_status_queue.get_nowait()
                self.status_var.set(message)
                self.root.update()
        except queue.Empty:
            pass
        self.root.after(100, self._process_queue)

    def run_ai_annotation_from_hotkey(self, event=None):
        """
        Runs AI annotation with the currently selected models, without opening a dialog.
        This is bound to the 'a' key.
        """
        if self._is_annotating_ai:
            self.status_var.set("AI annotation is already in progress.")
            return
        if not self.current_file_path:
            messagebox.showwarning("No File", "Please load a file first.", parent=self.root)
            return
        if not self.current_ai_models:
            messagebox.showwarning("No AI Models Set", "Please configure AI models first by going to Settings > Pre-annotate with AI...", parent=self.root)
            return

        # Start the process directly with the already configured models.
        self._start_ai_annotation_process(self.current_ai_models)

    def pre_annotate_with_ai(self):
        """
        This method is bound to the menu item. It always opens the dialog
        to allow the user to modify settings before running.
        """
        if self._is_annotating_ai:
            self.status_var.set("AI annotation is already in progress.")
            return
        if not self.current_file_path:
            messagebox.showwarning("No File", "Please load a file first.", parent=self.root)
            return

        # Always show the dialog when the menu item is clicked.
        self._show_ai_settings_dialog()

    def _show_ai_settings_dialog(self):
        """
        Creates and shows a dialog for AI model selection.
        """
        dialog = tk.Toplevel(self.root)
        dialog.title("AI Pre-annotation Settings")
        dialog.geometry("500x400")
        dialog.transient(self.root)
        dialog.grab_set()

        frame = tk.Frame(dialog, padx=10, pady=10)
        frame.pack(fill=tk.BOTH, expand=True)

        tk.Label(frame, text="Selected Models (max 2):").pack(anchor=tk.W, pady=(0, 5))

        # Listbox to show selected models
        selected_models_frame = tk.Frame(frame)
        selected_models_frame.pack(fill=tk.X)
        self.selected_models_listbox = tk.Listbox(selected_models_frame, height=2, exportselection=False)
        self.selected_models_listbox.pack(side=tk.LEFT, fill=tk.X, expand=True)
        selected_models_scrollbar = tk.Scrollbar(selected_models_frame, command=self.selected_models_listbox.yview)
        selected_models_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.selected_models_listbox.config(yscrollcommand=selected_models_scrollbar.set)

        # Initialize the listbox with the currently active models
        # Use a copy to prevent modifying the main list directly
        for model in self.current_ai_models:
            self.selected_models_listbox.insert(tk.END, model)

        def add_model_to_list(model_name):
            model_name = model_name.strip()
            if not model_name or model_name in self.selected_models_listbox.get(0, tk.END):
                return
            if self.selected_models_listbox.size() >= 2:
                messagebox.showwarning("Limit Exceeded", "You can only select up to 2 models.", parent=dialog)
                return
            self.selected_models_listbox.insert(tk.END, model_name)

        def remove_selected_model():
            selection = self.selected_models_listbox.curselection()
            if selection:
                self.selected_models_listbox.delete(selection[0])

        # Add/Remove buttons for the listbox
        listbox_buttons_frame = tk.Frame(frame)
        listbox_buttons_frame.pack(fill=tk.X, pady=(5, 10))
        tk.Button(listbox_buttons_frame, text="Remove Selected", command=remove_selected_model).pack(side=tk.RIGHT)

        # Model sources section
        tk.Label(frame, text="Choose a pre-trained model:").pack(anchor=tk.W, pady=(10, 5))
        models_frame = tk.Frame(frame)
        models_frame.pack(fill=tk.X)

        # Combobox for pre-defined models
        common_models = [
            "Babelscape/wikineural-multilingual-ner",
            "dslim/bert-base-NER",
            "magistermilitum/roberta-multilingual-medieval-ner"
        ]
        model_var = tk.StringVar(value="")
        model_combo = ttk.Combobox(models_frame, textvariable=model_var, values=common_models, state="readonly")
        model_combo.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=(0,5))
        tk.Button(models_frame, text="Add", command=lambda: add_model_to_list(model_var.get())).pack(side=tk.LEFT)

        # Entry for custom models
        tk.Label(frame, text="Custom model from Hugging Face:").pack(anchor=tk.W, pady=(10, 5))
        custom_model_var = tk.StringVar(value="")
        custom_model_entry = tk.Entry(frame, textvariable=custom_model_var)
        custom_model_entry.pack(fill=tk.X)
        tk.Button(frame, text="Add Custom", command=lambda: add_model_to_list(custom_model_var.get())).pack(anchor=tk.W, pady=(5,10))

        def on_start_annotate():
            model_names = list(self.selected_models_listbox.get(0, tk.END))
            if not model_names:
                messagebox.showwarning("No Model Selected", "Please select or enter at least one model.", parent=dialog)

                return

            dialog.destroy()
            self._set_ai_models(model_names) # Set the current models
            self._start_ai_annotation_process(self.current_ai_models) # Start the process with the new setting

        # Buttons
        btn_frame = tk.Frame(frame)
        btn_frame.pack(fill=tk.X, pady=(10, 0))
        tk.Button(btn_frame, text="Annotate", command=on_start_annotate).pack(side=tk.RIGHT)
        tk.Button(btn_frame, text="Cancel", command=dialog.destroy).pack(side=tk.RIGHT, padx=5)

        dialog.wait_window()

    def _set_ai_models(self, model_names):
        """Sets the current models and updates the history list."""
        self.current_ai_models = model_names
        # Update the last used models list
        for name in model_names:
            if name in self.last_used_ai_models:
                self.last_used_ai_models.remove(name)
            self.last_used_ai_models.insert(0, name)
        self.last_used_ai_models = self.last_used_ai_models[:5] # Keep the 5 most recent


    def _start_ai_annotation_process(self, model_names):
        """Starts the AI annotation process in a separate thread."""
        self._is_annotating_ai = True
        self.settings_menu.entryconfig("Pre-annotate with AI...", state="disabled")
        self._update_status_threadsafe(f"Loading AI model '{model_names[0]}'...")

        full_text = self.text_area.get("1.0", tk.END)
        pipelines = []

        try:
            from transformers import pipeline, AutoTokenizer
            AI_DEVICE = "cuda" if torch.cuda.is_available() else "cpu"

            for i, model_name in enumerate(model_names):
                self._update_status_threadsafe(f"Loading AI model '{model_name}' ({i+1}/{len(model_names)})...")

                tokenizer = AutoTokenizer.from_pretrained(model_name)
                ner_pipeline = pipeline(
                    "token-classification",
                    model=model_name,
                    tokenizer=tokenizer,
                    aggregation_strategy="max",
                    device=AI_DEVICE
                )
                pipelines.append(ner_pipeline)

            self._update_status_threadsafe("AI models loaded. Starting annotation...")

            threading.Thread(
                target=self._run_ai_model,
                args=(full_text, pipelines),
                daemon=True
            ).start()

        except ImportError as e:
            self._is_annotating_ai = False
            self.settings_menu.entryconfig("Pre-annotate with AI...", state="normal")
            messagebox.showerror(
                "Missing Libraries",
                "The 'transformers' and 'torch' libraries are required.\nPlease install: pip install transformers torch",
                parent=self.root
            )
            self._update_status_threadsafe("AI pre-annotation failed due to missing libraries.")
        except Exception as e:
            self._is_annotating_ai = False
            self.settings_menu.entryconfig("Pre-annotate with AI...", state="normal")
            messagebox.showerror(
                "Model Load Error",
                f"Failed to load one or more models. Please check the model name(s) and internet connection.\n\nError: {e}",
                parent=self.root
            )
            self._update_status_threadsafe("AI pre-annotation failed due to model loading error.")
            traceback.print_exc()

    def _run_ai_model(self, full_text, pipelines):
        """
        Applies NER models to long text and merges the results.
        """
        try:
            label_map = {
                "PER": "Person", "I-PER": "Person", "B-PER": "Person",
                "ORG": "Organization", "I-ORG": "Organization", "B-ORG": "Organization",
                "LOC": "Location", "I-LOC": "Location", "B-LOC": "Location",
                "DATE": "Date", "I-DATE": "Date", "B-DATE": "Date",
                "MISC": "Other", "I-MISC": "Other", "B-MISC": "Other"
            }

            all_detected_entities = []

            for i, ner_pipeline in enumerate(pipelines):
                self._update_status_threadsafe(f"Annotating with model {i+1}/{len(pipelines)}...")

                # We will process the whole text at once if possible, or chunk if needed.
                # The tokenizer used for chunking is the one from the first pipeline,
                # as all models are assumed to be from Hugging Face and have a tokenizer.
                tokenizer = ner_pipeline.tokenizer
                max_length = tokenizer.model_max_length if hasattr(tokenizer, 'model_max_length') else 512
                stride = 128

                if len(full_text) < max_length * 2: # Simple text, no need for chunking
                    chunk_results = ner_pipeline(full_text)
                    for entity in chunk_results:
                        tag = label_map.get(entity.get("entity_group"))
                        if not tag or tag not in self.entity_tags: continue

                        start_offset_raw = entity['start']
                        end_offset_raw = entity['end']

                        # Fix the whitespace issue
                        entity_text_raw = full_text[start_offset_raw:end_offset_raw]
                        lstrip_len = len(entity_text_raw) - len(entity_text_raw.lstrip())
                        rstrip_len = len(entity_text_raw) - len(entity_text_raw.rstrip())

                        start_offset_clean = start_offset_raw + lstrip_len
                        end_offset_clean = end_offset_raw - rstrip_len

                        final_word = full_text[start_offset_clean:end_offset_clean]
                        if not final_word.strip(): continue

                        start_pos = self._char_offset_to_tkinter_index(full_text, start_offset_clean)
                        end_pos = self._char_offset_to_tkinter_index(full_text, end_offset_clean)
                        start_line, start_char = map(int, start_pos.split("."))
                        end_line, end_char = map(int, end_pos.split("."))

                        # Check if the text matches the clean text
                        if self.text_area.get(start_pos, end_pos).strip() != final_word.strip():
                            # This is a fallback in case the offset mapping is tricky
                            start_pos = self._find_start_of_word(full_text, start_offset_clean)
                            end_pos = self._find_end_of_word(full_text, end_offset_clean)
                            start_line, start_char = map(int, start_pos.split('.'))
                            end_line, end_char = map(int, end_pos.split('.'))
                            final_word = self.text_area.get(start_pos, end_pos).strip()
                            if not final_word: continue

                        new_ann = {
                            "id": uuid.uuid4().hex,
                            "start_line": start_line, "start_char": start_char,
                            "end_line": end_line, "end_char": end_char,
                            "text": final_word, "tag": tag, "propagated": True,
                        }
                        all_detected_entities.append(new_ann)

                else: # Chunking for long texts
                    encoding = tokenizer(
                        full_text,
                        return_offsets_mapping=True,
                        add_special_tokens=False,
                        truncation=False
                    )
                    all_offsets = encoding['offset_mapping']
                    all_tokens = encoding['input_ids']

                    num_tokens = len(all_tokens)
                    num_chunks = -(-num_tokens // (max_length - stride)) if (max_length - stride) > 0 else 1

                    for j in range(0, num_tokens, max_length - stride):
                        self._update_status_threadsafe(f"Model {i+1}/{len(pipelines)}: Chunk {j // (max_length - stride) + 1}/{num_chunks}...")

                        start_token_idx = j
                        end_token_idx = min(j + max_length, num_tokens)
                        if start_token_idx >= end_token_idx: continue

                        chunk_start_char = all_offsets[start_token_idx][0]
                        chunk_end_char = all_offsets[end_token_idx - 1][1]
                        chunk_text = full_text[chunk_start_char:chunk_end_char]
                        if not chunk_text.strip(): continue

                        chunk_results = ner_pipeline(chunk_text)

                        for entity in chunk_results:
                            tag = label_map.get(entity.get("entity_group"))
                            if not tag or tag not in self.entity_tags: continue

                            start_offset_raw = chunk_start_char + entity['start']
                            end_offset_raw = chunk_start_char + entity['end']

                            # Fix the whitespace issue
                            entity_text_raw = full_text[start_offset_raw:end_offset_raw]
                            lstrip_len = len(entity_text_raw) - len(entity_text_raw.lstrip())
                            rstrip_len = len(entity_text_raw) - len(entity_text_raw.rstrip())

                            start_offset_clean = start_offset_raw + lstrip_len
                            end_offset_clean = end_offset_raw - rstrip_len

                            final_word = full_text[start_offset_clean:end_offset_clean]
                            if not final_word.strip(): continue

                            start_pos = self._char_offset_to_tkinter_index(full_text, start_offset_clean)
                            end_pos = self._char_offset_to_tkinter_index(full_text, end_offset_clean)
                            start_line, start_char = map(int, start_pos.split("."))
                            end_line, end_char = map(int, end_pos.split("."))

                            if self.extend_to_word.get():
                                start_pos_word = self.text_area.index(f"{start_line}.{start_char} wordstart")
                                end_pos_word = self.text_area.index(f"{end_line}.{end_char} wordend")
                                start_line, start_char = map(int, start_pos_word.split("."))
                                end_line, end_char = map(int, end_pos_word.split("."))

                                start_offset_word = self._tkinter_index_to_char_offset(full_text, start_line, start_char)
                                end_offset_word = self._tkinter_index_to_char_offset(full_text, end_line, end_char)
                                final_word = full_text[start_offset_word:end_offset_word].strip()
                                if not final_word: continue

                            new_ann = {
                                "id": uuid.uuid4().hex,
                                "start_line": start_line,
                                "start_char": start_char,
                                "end_line": end_line,
                                "end_char": end_char,
                                "text": final_word,
                                "tag": tag,
                                "propagated": True,
                            }
                            all_detected_entities.append(new_ann)

            # De-duplicate entities found across all models and overlapping regions
            unique_annotations_dict = {}
            for ann in sorted(all_detected_entities, key=lambda x: len(x['text']), reverse=True):
                key = (ann['start_line'], ann['start_char'], ann['end_line'], ann['end_char'], ann['tag'])
                if key not in unique_annotations_dict:
                    unique_annotations_dict[key] = ann

            new_annotations = list(unique_annotations_dict.values())
            self.root.after(0, self._update_ui_with_ai_annotations, new_annotations)

        except Exception as e:
            self.root.after(0, self.status_var.set, "AI pre-annotation failed. See console for details.")
            traceback.print_exc()
        finally:
            if hasattr(self, '_is_annotating_ai'):
                self._is_annotating_ai = False
            self.root.after(0, self.settings_menu.entryconfig, "Pre-annotate with AI...", {"state": "normal"})

    def _find_start_of_word(self, text, char_offset):
        """Finds the start of the word from a given character offset."""
        while char_offset > 0 and text[char_offset-1].isalnum():
            char_offset -= 1
        return self._char_offset_to_tkinter_index(text, char_offset)

    def _find_end_of_word(self, text, char_offset):
        """Finds the end of the word from a given character offset."""
        while char_offset < len(text) and text[char_offset].isalnum():
            char_offset += 1
        return self._char_offset_to_tkinter_index(text, char_offset)


    def _char_offset_to_tkinter_index(self, text, offset):
        """Helper function to convert a character offset to a Tkinter 'line.char' index."""
        line_start = text.rfind('\n', 0, offset) + 1
        line = text.count('\n', 0, offset) + 1
        char = offset - line_start
        return f"{line}.{char}"

    def _update_ui_with_ai_annotations(self, new_annotations):
        """Adds the AI-generated annotations to the main data structure and refreshes the UI."""
        try:
            if not new_annotations:
                self.status_var.set("AI pre-annotation complete. No new entities found.")
                return

            entities_list = self.annotations.setdefault(self.current_file_path, {}).setdefault("entities", [])
            added_count = 0
            for ann in new_annotations:
                # Check for exact duplicate before adding
                is_duplicate = any(
                    e['start_line'] == ann['start_line'] and
                    e['start_char'] == ann['start_char'] and
                    e['end_line'] == ann['end_line'] and
                    e['end_char'] == ann['end_char'] and
                    e['tag'] == ann['tag']
                    for e in entities_list
                )

                if not is_duplicate and (self.allow_multilabel_overlap.get() or not self._is_overlapping_in_list(ann['start_line'], ann['start_char'], ann['end_line'], ann['end_char'], entities_list)):
                    entities_list.append(ann)
                    added_count += 1

            # Sort the final list of entities for consistent display
            entities_list.sort(key=lambda a: (a['start_line'], a['start_char']))

            self.apply_annotations_to_text()
            self.update_entities_list()
            self.status_var.set(f"AI pre-annotation complete. Added {added_count} new entities.")
        finally:
            self.settings_menu.entryconfig("Pre-annotate with AI...", state="normal")
            self._is_annotating_ai = False

def main():
    root = tk.Tk()
    try:
        style = ttk.Style()
        themes = style.theme_names()
        # Prefer more modern themes if available
        preferred_themes = ['clam', 'alt', 'vista', 'xpnative'] # Add more modern themes if known
        # Fallback to 'default' if no preferred themes are found
        # Or use style.theme_use(style.theme_names()[0]) for the first available theme

        current_theme = style.theme_use() # Get current theme to check if it's already good

        # If current theme is not in our preferred list, try to set one
        if current_theme not in preferred_themes:
            for t in preferred_themes:
                if t in themes:
                    try:
                        style.theme_use(t)
                        break # Stop if a preferred theme is successfully applied
                    except tk.TclError:
                        continue # Try next theme if current one fails
            else: # If loop completes without break (no preferred theme worked or was found)
                if 'default' in themes : style.theme_use('default')
                # If 'default' is also not available, it will use the system default

    except tk.TclError:
        print("ttk themes not available or failed to apply.")
        # The application will still run with the default Tk look and feel.

    app = TextAnnotator(root)
    root.mainloop()

if __name__ == "__main__":
    main()
