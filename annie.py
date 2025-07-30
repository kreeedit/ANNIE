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
import re
import shutil # For high-level file operations, copying
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import json
from pathlib import Path
import uuid # For unique IDs
import itertools # For cycling through colors
import traceback # For more detailed error printing
import time


# --- Constants ---
SESSION_FILE_VERSION = "1.11"

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
        self.files_list = [] # List of *full paths* to text files
        self.current_file_index = -1
        self.annotations = {}
        self.session_save_path = None

        # --- Entity Tagging Configuration ---
        self.entity_tags = ["Person", "Organization", "Location", "Date", "Other"]
        self.selected_entity_tag = tk.StringVar(value=self.entity_tags[0] if self.entity_tags else "")
        self.extend_to_word = tk.BooleanVar(value=False)
        self.allow_multilabel_overlap = tk.BooleanVar(value=False)

        # --- Relation Tagging Configuration ---
        self.relation_types = ["spouse_of", "works_at", "located_in", "born_on", "produces"]
        self.selected_relation_type = tk.StringVar(value=self.relation_types[0] if self.relation_types else "")

        # --- UI State ---
        self.selected_entity_ids_for_relation = []
        self._entity_id_to_tree_iids = {}
        self._click_time = 0
        self._click_pos = (0, 0)
        self._is_deleting = False

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

        # --- Initial UI Setup ---
        self._update_entity_tag_combobox()
        self._update_relation_type_combobox()
        self._configure_text_tags()
        self._configure_treeview_tags()
        self._update_button_states()

        # --- Bind Hotkeys ---
        for i in range(10): # Binds keys 0-9
            self.root.bind(str(i), self._on_hotkey_press)

        self.root.protocol("WM_DELETE_WINDOW", self._on_closing)

    def _ensure_default_colors(self):
        for tag in self.entity_tags:
            self.get_color_for_tag(tag)

    def _on_mouse_down(self, event):
        """Records the time and position of a mouse press."""
        self._click_time = time.time()
        self._click_pos = (event.x, event.y)

    def _on_hotkey_press(self, event):
        """Handles number key presses to select an entity tag."""
        try:
            # The key '1' corresponds to index 0, '2' to 1, ..., '9' to 8, and '0' to 9.
            key_num = int(event.keysym)
            tag_index = (key_num - 1) % 10

            # Check if the corresponding tag exists
            if 0 <= tag_index < len(self.entity_tags):
                selected_tag = self.entity_tags[tag_index]
                self.selected_entity_tag.set(selected_tag)
                self.status_var.set(f"Selected Tag: {selected_tag}")
                return "break" # Prevents the key press from propagating further
        except (ValueError, IndexError):
            # Key pressed was not a number or tag doesn't exist. Do nothing.
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
        file_menu.add_command(label="Save Annotations Only...", command=self.save_annotations)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self._on_closing)
        menubar.add_cascade(label="File", menu=file_menu)

        settings_menu = tk.Menu(menubar, tearoff=0)
        settings_menu.add_command(label="Manage Entity Tags...", command=self.manage_entity_tags)
        settings_menu.add_command(label="Manage Relation Types...", command=self.manage_relation_types)
        settings_menu.add_separator()
        settings_menu.add_command(label="Load Dictionary & Propagate Entities...", command=self.load_and_propagate_from_dictionary)
        settings_menu.add_separator()
        settings_menu.add_checkbutton(
            label="Allow Multi-label & Overlapping Annotations",
            variable=self.allow_multilabel_overlap,
            onvalue=True, offvalue=False
        )
        menubar.add_cascade(label="Settings", menu=settings_menu)

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
            insertbackground="black", insertwidth=2,
            borderwidth=1, relief="sunken",
        )
        self.text_area.pack(fill=tk.BOTH, expand=True)
        scrollbar_text_y.config(command=self.text_area.yview)
        scrollbar_text_x.config(command=self.text_area.xview)

        self.text_area.bind("<ButtonPress-1>", self._on_mouse_down)
        self.text_area.bind("<ButtonRelease-1>", self._on_highlight_release)
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
        self.propagate_btn = tk.Button(ecf_bottom, text="Propagate Entities (Current File)", command=self.propagate_annotations, state=tk.DISABLED)
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

        tree_columns = tree["columns"]
        display_columns = tree["displaycolumns"] if tree["displaycolumns"] != "#all" else tree_columns
        for column_id in display_columns:
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
        current_idx = -1
        if focused_item and focused_item in all_items:
            try: current_idx = all_items.index(focused_item)
            except ValueError: current_idx = -1
        match_column = "Text" if tree == self.entities_tree else "Head"
        start_idx = (current_idx + 1) % len(all_items) if current_idx >= 0 else 0
        found_idx = None
        for i in range(start_idx, len(all_items)):
            item_id = all_items[i]
            item_text = str(tree.set(item_id, match_column)).lower()
            if item_text.startswith(char):
                found_idx = i; break
        if found_idx is None:
            for i in range(0, start_idx):
                item_id = all_items[i]
                item_text = str(tree.set(item_id, match_column)).lower()
                if item_text.startswith(char):
                    found_idx = i; break
        if found_idx is not None:
            found_item = all_items[found_idx]
            if tree.exists(found_item):
                tree.selection_set(found_item)
                tree.focus(found_item)
                tree.see(found_item)
                if tree == self.entities_tree: self.on_entity_select(None)
                else: self.on_relation_select(None)
                return "break"

    def _on_highlight_release(self, event):
        """
        Handles both creating annotations on drag-release and removing them on a simple click.
        Distinguishes a click from a drag using time and distance thresholds.
        """
        if not self.current_file_path:
            return

        # --- Define thresholds for what constitutes a "click" ---
        CLICK_TIME_THRESHOLD = 0.5  # seconds
        CLICK_MOVE_THRESHOLD = 10    # pixels

        time_diff = time.time() - self._click_time
        move_diff = abs(event.x - self._click_pos[0]) + abs(event.y - self._click_pos[1])

        # --- Logic for creating a new annotation via highlighting ---
        try:
            sel_start = self.text_area.index(tk.SEL_FIRST)
            sel_end = self.text_area.index(tk.SEL_LAST)
            # If there's a real selection (a drag), annotate it.
            if sel_start != sel_end:
                self.annotate_selection()
                return # Annotation handled, so we are done.
        except tk.TclError:
            # This is expected if there was no drag-selection.
            pass

        # --- Logic for removing an existing annotation on a quick click ---
        if time_diff < CLICK_TIME_THRESHOLD and move_diff < CLICK_MOVE_THRESHOLD:
            try:
                click_index_str = self.text_area.index(f"@{event.x},{event.y}")
                click_line, click_char = map(int, click_index_str.split('.'))
                click_pos = (click_line, click_char)

                clicked_entity_dict = None
                entities = self.annotations.get(self.current_file_path, {}).get("entities", [])

                # Iterate reversed to find the "topmost" annotation if they overlap
                for entity in reversed(entities):
                    start_l, start_c = entity.get('start_line'), entity.get('start_char')
                    end_l, end_c = entity.get('end_line'), entity.get('end_char')
                    if None in [start_l, start_c, end_l, end_c]: continue

                    if (start_l, start_c) <= click_pos < (end_l, end_c):
                        clicked_entity_dict = entity
                        break

                if clicked_entity_dict:
                    self._remove_entity_instance(clicked_entity_dict)

            except tk.TclError: # Clicked outside text area content
                pass
            except Exception as e:
                print(f"Error during single-click check: {e}")


    def _remove_entity_instance(self, entity_to_remove):
        if not self.current_file_path or self.current_file_path not in self.annotations:
            return
        file_data = self.annotations[self.current_file_path]
        entities_list = file_data.get("entities", [])
        relations_list = file_data.get("relations", [])
        entity_index_to_remove = -1
        # Try to find the exact dictionary instance first for robustness
        try:
            entity_index_to_remove = entities_list.index(entity_to_remove)
        except ValueError: # Fallback to matching by content if the exact instance isn't found (e.g., if a copy was passed)
            for i, entity in enumerate(entities_list):
                if (entity.get('id') == entity_to_remove.get('id') and
                    entity.get('start_line') == entity_to_remove.get('start_line') and
                    entity.get('start_char') == entity_to_remove.get('start_char') and
                    entity.get('end_line') == entity_to_remove.get('end_line') and
                    entity.get('end_char') == entity_to_remove.get('end_char') and
                    entity.get('tag') == entity_to_remove.get('tag')): # Added tag match for more precision
                    entity_index_to_remove = i
                    break
        if entity_index_to_remove == -1:
            messagebox.showerror("Error", "Could not find the clicked entity instance to remove.", parent=self.root)
            return

        entity_id_being_removed = entities_list[entity_index_to_remove].get('id') # Use ID from the found entity
        entity_text = entities_list[entity_index_to_remove].get('text', '')[:30]
        entity_tag_being_removed = entities_list[entity_index_to_remove].get('tag', 'N/A')

        confirm = messagebox.askyesno("Confirm Removal",
                                    f"Remove annotation for '{entity_text}...' ({entity_tag_being_removed})?\n"
                                    f"(Instance ID: {entity_id_being_removed[:8]}...)\n"
                                    f"WARNING: May remove associated relations if this is the last instance of this ID.",
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

        # Configure a tag for a prominent selection border
        self.text_area.tag_configure("selection_highlight", borderwidth=1, relief=tk.SOLID)


    def _configure_treeview_tags(self):
        try:
            self.entities_tree.tag_configure(
                'merged',
                foreground='grey',
                font=('TkDefaultFont', 9, 'italic')
            )
        except tk.TclError as e:
            print(f"Warning: Could not configure Treeview tags: {e}")


    def _update_entity_tag_combobox(self):
        current_selection = self.selected_entity_tag.get()
        if not self.entity_tags:
            self.selected_entity_tag.set("")
            self.entity_tag_combobox.config(values=[], state=tk.DISABLED)
        else:
            self.entity_tag_combobox['values'] = self.entity_tags
            if current_selection not in self.entity_tags or self.entity_tag_combobox['state'] == tk.DISABLED:
                self.selected_entity_tag.set(self.entity_tags[0])
            else:
                self.selected_entity_tag.set(current_selection)
            self.entity_tag_combobox.config(state="readonly")


    def _update_relation_type_combobox(self):
        current_selection = self.selected_relation_type.get()
        if not self.relation_types:
            self.selected_relation_type.set("")
            self.relation_type_combobox.config(values=[], state=tk.DISABLED)
        else:
            self.relation_type_combobox['values'] = self.relation_types
            if current_selection not in self.relation_types or self.relation_type_combobox['state'] == tk.DISABLED:
                self.selected_relation_type.set(self.relation_types[0])
            else:
                self.selected_relation_type.set(current_selection)
            self.relation_type_combobox.config(state="readonly")


    def _update_button_states(self):
        file_loaded = bool(self.current_file_path)
        has_files = bool(self.files_list)
        num_entities_selected_rows = len(self.entities_tree.selection())
        num_relations_selected = len(self.relations_tree.selection())
        self.prev_btn.config(state=tk.NORMAL if has_files and self.current_file_index > 0 else tk.DISABLED)
        self.next_btn.config(state=tk.NORMAL if has_files and self.current_file_index < len(self.files_list) - 1 else tk.DISABLED)
        can_annotate_entity_button = file_loaded and self.entity_tags
        self.annotate_btn.config(state=tk.NORMAL if can_annotate_entity_button else tk.DISABLED)
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
                self.session_save_path = None
                self.files_listbox.delete(0, tk.END)
                for file_path in self.files_list:
                    self.files_listbox.insert(tk.END, os.path.basename(file_path))
                self.load_file(0)
                self.status_var.set(f"Loaded {len(self.files_list)} files from '{os.path.basename(directory)}'")
                self.root.title(f"ANNIE - {os.path.basename(directory)}")
            else:
                self.status_var.set(f"No .txt files found in '{os.path.basename(directory)}'")
                self.files_listbox.delete(0, tk.END)
            self._update_button_states()

    def add_files_to_session(self):
        """Allows adding new text files to the current session."""
        if not self.files_list:
            messagebox.showwarning("No Session Active", "Please open a directory or load a session first.", parent=self.root)
            return

        source_paths = filedialog.askopenfilenames(
            title="Select Text File(s) to Add",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")],
            parent=self.root
        )
        if not source_paths:
            self.status_var.set("Add files cancelled.")
            return

        # Determine the session's working directory from the first file
        destination_dir = os.path.dirname(self.files_list[0])
        current_basenames = {os.path.basename(p) for p in self.files_list}
        added_count = 0

        for source_path in source_paths:
            basename = os.path.basename(source_path)
            dest_path = os.path.join(destination_dir, basename)

            # Check for conflicts
            if basename in current_basenames:
                messagebox.showwarning("File Exists", f"A file named '{basename}' is already in this session. Skipping.", parent=self.root)
                continue

            # Copy the file to the session directory if it's not already there
            if os.path.abspath(source_path) != os.path.abspath(dest_path):
                try:
                    shutil.copy2(source_path, dest_path)
                except Exception as e:
                    messagebox.showerror("Copy Error", f"Could not copy file '{basename}' to session directory.\n\nError: {e}", parent=self.root)
                    continue

            # Add the new file (using its destination path) to the session
            self.files_list.append(dest_path)
            self.files_listbox.insert(tk.END, basename)
            current_basenames.add(basename)
            added_count += 1

        if added_count > 0:
            # Sort the master list and refresh the UI listbox
            current_selection_path = self.current_file_path
            self.files_list.sort(key=lambda p: os.path.basename(p).lower())

            self.files_listbox.delete(0, tk.END)
            for path in self.files_list:
                self.files_listbox.insert(tk.END, os.path.basename(path))

            # Re-select the previously active file
            if current_selection_path in self.files_list:
                new_index = self.files_list.index(current_selection_path)
                self.files_listbox.selection_set(new_index)
                self.files_listbox.see(new_index)
                self.files_listbox.activate(new_index)

            self._update_button_states()
            self.status_var.set(f"Successfully added {added_count} file(s) to the session.")


    def load_file(self, index):
        if not (0 <= index < len(self.files_list)):
            print(f"Warning: Invalid file index {index} requested.")
            return
        if index == self.current_file_index and self.current_file_path:
            return
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
        file_loaded_successfully = False
        try:
            with open(self.current_file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                self.text_area.insert(tk.END, content)
            file_loaded_successfully = True
        except Exception as e:
            messagebox.showerror("Error Reading File", f"Failed to load file '{filename}':\n{str(e)}", parent=self.root)
            self.text_area.delete(1.0, tk.END)
            self.text_area.config(state=tk.DISABLED)
            self.current_file_path = None
            self.status_var.set(f"Error loading {filename}")
            file_loaded_successfully = False
            try: self.entities_tree.delete(*self.entities_tree.get_children())
            except Exception: pass
            try: self.relations_tree.delete(*self.relations_tree.get_children())
            except Exception: pass
            self.selected_entity_ids_for_relation = []
        if file_loaded_successfully:
            file_data = self.annotations.setdefault(self.current_file_path, {"entities": [], "relations": []})
            file_data.setdefault("entities", [])
            file_data.setdefault("relations", [])
            self.update_entities_list()
            self.update_relations_list()
            self.apply_annotations_to_text()
            self.status_var.set(f"Loaded: {filename} ({index+1}/{len(self.files_list)})")
            self.text_area.edit_reset()
            self.text_area.config(state=tk.DISABLED)
        self._update_button_states()


    def clear_views(self):
        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL)
        try:
            self.text_area.delete(1.0, tk.END)
            current_text_tags = list(self.text_area.tag_names())
            tags_to_remove = set(self.entity_tags)
            tags_to_remove.add("propagated_entity")
            for tag_name in current_text_tags:
                if tag_name in tags_to_remove and tag_name != tk.SEL:
                    try: self.text_area.tag_remove(tag_name, "1.0", tk.END)
                    except tk.TclError: pass
            try: self.text_area.tag_remove(tk.SEL, "1.0", tk.END)
            except tk.TclError: pass
        finally:
            if self.text_area.winfo_exists():
                 self.text_area.config(state=tk.DISABLED if not self.current_file_path else original_state)
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
        if self.text_area.winfo_exists():
            self.text_area.config(state=tk.DISABLED)


    def load_next_file(self):
        if self.files_list and self.current_file_index < len(self.files_list) - 1:
            self.load_file(self.current_file_index + 1)


    def load_previous_file(self):
        if self.files_list and self.current_file_index > 0:
            self.load_file(self.current_file_index - 1)


    def on_file_select(self, event):
        selected_indices = self.files_listbox.curselection()
        if selected_indices:
            index = selected_indices[0]
            if index != self.current_file_index:
                self.load_file(index)


    def save_annotations(self):
        if not self.annotations or all(not data.get('entities') and not data.get('relations') for data in self.annotations.values()):
            messagebox.showinfo("Info", "There are no annotations to save.", parent=self.root)
            return
        initial_dir = os.path.dirname(self.files_list[0]) if self.files_list else ""
        initial_file = "annotations_only.json"
        if initial_dir:
            dir_name = os.path.basename(initial_dir)
            if dir_name: initial_file = f"{dir_name}_annotations_only.json"
        save_path = filedialog.asksaveasfilename(
            initialdir=initial_dir, initialfile=initial_file, defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
            title="Save Annotations ONLY As", parent=self.root
        )
        if not save_path:
            self.status_var.set("Save annotations cancelled."); return
        save_dir = os.path.dirname(save_path)
        serializable_annotations = {}
        for file_path, data in self.annotations.items():
            entities = data.get("entities", [])
            relations = data.get("relations", [])
            if not entities and not relations: continue
            key = file_path
            try:
                rel_path = os.path.relpath(file_path, start=save_dir)
                use_rel_path = False
                try:
                    if Path(file_path).resolve().is_relative_to(Path(save_dir).resolve()): use_rel_path = True
                except AttributeError:
                    if not os.path.isabs(rel_path) and not rel_path.startswith(('..'+os.sep, '..'+'/')):
                        use_rel_path = True
                if use_rel_path: key = rel_path.replace('\\', '/')
                else: key = os.path.basename(file_path)
            except ValueError: key = os.path.basename(file_path)
            except Exception as e:
                print(f"Warning: Relative path calculation error: {e}. Using basename for '{file_path}'.")
                key = os.path.basename(file_path)
            sorted_entities = sorted(entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0)))
            sorted_relations = sorted(relations, key=lambda r: (r.get('type', ''), r.get('head_id','')))
            serializable_annotations[key] = { "entities": sorted_entities, "relations": sorted_relations }
        try:
            with open(save_path, 'w', encoding='utf-8') as f:
                json.dump(serializable_annotations, f, indent=2, ensure_ascii=False)
            self.status_var.set(f"Annotations ONLY saved to '{os.path.basename(save_path)}'")
        except Exception as e:
            messagebox.showerror("Save Error", f"Could not write annotations to file:\n{e}", parent=self.root)
            self.status_var.set("Error saving annotations.")


    def save_session(self, force_ask=False):
        if not self.files_list:
            messagebox.showwarning("Cannot Save Session", "Please open a directory first.", parent=self.root)
            return
        save_path = self.session_save_path
        if force_ask or not save_path:
            initial_dir = os.path.dirname(self.files_list[0]) if self.files_list else ""
            initial_file = "annie_session.json"
            if initial_dir:
                dir_name = os.path.basename(initial_dir)
                if dir_name: initial_file = f"{dir_name}_session.json"
            save_path = filedialog.asksaveasfilename(
                initialdir=initial_dir, initialfile=initial_file, defaultextension=".json",
                filetypes=[("ANNIE Session files", "*.json"), ("All files", "*.*")],
                title="Save Session As", parent=self.root
            )
        if not save_path:
            self.status_var.set("Save session cancelled."); return
        session_data = {
            "version": SESSION_FILE_VERSION,
            "files_list": self.files_list,
            "current_file_index": self.current_file_index,
            "entity_tags": self.entity_tags,
            "relation_types": self.relation_types,
            "tag_colors": self.tag_colors,
            "annotations": self.annotations,
            "extend_to_word": self.extend_to_word.get(),
            "allow_multilabel_overlap": self.allow_multilabel_overlap.get()
        }
        try:
            with open(save_path, 'w', encoding='utf-8') as f:
                json.dump(session_data, f, indent=2, ensure_ascii=False)
            self.session_save_path = save_path
            self.status_var.set(f"Session saved to '{os.path.basename(save_path)}'")
            base_dir_name = "Session"
            if self.files_list:
                try: base_dir_name = os.path.basename(os.path.dirname(self.files_list[0]))
                except: pass
            self.root.title(f"ANNIE - {base_dir_name} [{os.path.basename(save_path)}]")
        except Exception as e:
            messagebox.showerror("Save Session Error", f"Could not write session file:\n{e}", parent=self.root)
            self.status_var.set("Error saving session.")
            self.session_save_path = None


    def load_session(self):
        if self._has_unsaved_changes():
            if not messagebox.askyesno("Unsaved Changes", "You have unsaved changes.\nDiscard and load session?", parent=self.root):
                return
        load_path = filedialog.askopenfilename(
            defaultextension=".json", filetypes=[("ANNIE Session files", "*.json"), ("All files", "*.*")],
            title="Load Session", parent=self.root
        )
        if not load_path:
            self.status_var.set("Load session cancelled."); return
        try:
            with open(load_path, 'r', encoding='utf-8') as f: session_data = json.load(f)
        except Exception as e:
            messagebox.showerror("Load Session Error", f"Could not read session file:\n{e}", parent=self.root)
            return
        required_keys = ["version", "files_list", "current_file_index",
                         "entity_tags", "relation_types", "tag_colors", "annotations"]
        if not all(key in session_data for key in required_keys):
            messagebox.showerror("Load Session Error", "Session file is missing required data.", parent=self.root); return
        if not isinstance(session_data.get("files_list"), list) or \
           not isinstance(session_data.get("current_file_index"), int) or \
           not isinstance(session_data.get("annotations"), dict) or \
           not isinstance(session_data.get("entity_tags"), list) or \
           not isinstance(session_data.get("relation_types"), list) or \
           not isinstance(session_data.get("tag_colors"), dict):
            messagebox.showerror("Load Session Error", "Session file contains data with incorrect types.", parent=self.root); return
        loaded_files_list = session_data["files_list"]
        missing_files = [fp for fp in loaded_files_list if not os.path.isfile(fp)]
        if missing_files:
            msg = "Some text files referenced in the session could not be found:\n"
            msg += "\n".join([f"- {os.path.basename(mf)}" for mf in missing_files[:5]])
            if len(missing_files) > 5: msg += "\n..."
            msg += "\n\nAnnotations for missing files will be kept but files won't load.\nContinue loading session?"
            if not messagebox.askyesno("Missing Files", msg, parent=self.root):
                self.status_var.set("Load session cancelled due to missing files."); return
        self._reset_state()
        try:
            self.files_list = loaded_files_list
            self.current_file_index = session_data["current_file_index"]
            self.annotations = session_data["annotations"]
            self.entity_tags = session_data["entity_tags"]
            self.relation_types = session_data["relation_types"]
            self.tag_colors = session_data["tag_colors"]
            self.extend_to_word.set(session_data.get("extend_to_word", False))
            self.allow_multilabel_overlap.set(session_data.get("allow_multilabel_overlap", False))
            self.session_save_path = load_path
            self.files_listbox.delete(0, tk.END)
            for file_path in self.files_list:
                display_name = os.path.basename(file_path)
                if file_path in missing_files: display_name += " [MISSING]"
                self.files_listbox.insert(tk.END, display_name)
            if not (0 <= self.current_file_index < len(self.files_list)):
                self.current_file_index = 0 if self.files_list else -1
            self._update_entity_tag_combobox(); self._update_relation_type_combobox()
            self._configure_text_tags(); self._configure_treeview_tags()
            if self.current_file_index != -1:
                if self.files_list[self.current_file_index] in missing_files:
                    self.status_var.set(f"Session loaded. Current file '{os.path.basename(self.files_list[self.current_file_index])}' is missing.")
                    self.clear_views()
                    self.files_listbox.selection_clear(0, tk.END)
                    self.files_listbox.selection_set(self.current_file_index)
                    self.files_listbox.activate(self.current_file_index)
                    self.files_listbox.see(self.current_file_index)
                    self._update_button_states()
                else:
                    current_idx_temp = self.current_file_index
                    self.current_file_index = -1
                    self.load_file(current_idx_temp)
            else:
                self.status_var.set("Session loaded, but no files to display.")
                self.clear_views(); self._update_button_states()
            base_dir_name = "Session"
            if self.files_list:
                try: base_dir_name = os.path.basename(os.path.dirname(self.files_list[0]))
                except: pass
            self.root.title(f"ANNIE - {base_dir_name} [{os.path.basename(load_path)}]")
        except Exception as e:
            messagebox.showerror("Load Session Error", f"Error applying session data:\n{e}", parent=self.root)
            self._reset_state(); self._update_button_states()


    def _has_unsaved_changes(self):
        return bool(self.files_list)


    def _on_closing(self):
        if self._has_unsaved_changes():
            response = messagebox.askyesnocancel("Exit Confirmation", "You have an active session.\nSave session before exiting?", parent=self.root)
            if response is True:
                self.save_session()
                if self.session_save_path and "saved to" in self.status_var.get().lower():
                     self.root.quit()
            elif response is False:
                self.root.quit()
        else:
            self.root.quit()


    def _spans_overlap_numeric(self, start1_line, start1_char, end1_line, end1_char,
                               start2_line, start2_char, end2_line, end2_char):
        span1_start = (start1_line, start1_char)
        span1_end = (end1_line, end1_char)
        span2_start = (start2_line, start2_char)
        span2_end = (end2_line, end2_char)
        is_disjoint = (span1_end <= span2_start) or (span1_start >= span2_end)
        return not is_disjoint


    def _is_overlapping_in_list(self, start_line, start_char, end_line, end_char, existing_entities_list):
        for ann in existing_entities_list:
            if not all(k in ann for k in ['start_line', 'start_char', 'end_line', 'end_char']): continue
            if self._spans_overlap_numeric(start_line, start_char, end_line, end_char,
                                           ann['start_line'], ann['start_char'], ann['end_line'], ann['end_char']):
                return True
        return False


    def annotate_selection(self):
        if not self.current_file_path: return
        if not self.entity_tags:
            messagebox.showwarning("Warning", "No entity tags defined.", parent=self.root); return

        original_state = self.text_area.cget('state')
        needs_re_disable = False
        if original_state == tk.DISABLED:
            try:
                self.text_area.config(state=tk.NORMAL)
                needs_re_disable = True
            except tk.TclError:
                print("Warning: Could not enable text area state for annotation.")
                return

        try:
            start_pos = self.text_area.index(tk.SEL_FIRST)
            end_pos = self.text_area.index(tk.SEL_LAST)
            if start_pos == end_pos: # No actual selection range
                if needs_re_disable: self.text_area.config(state=tk.DISABLED)
                return

            # --- NEW: Snap the selection to whole word boundaries ---
            # This replaces the old, complex whitespace stripping logic.
            adj_start_pos = self.text_area.index(f"{start_pos} wordstart")
            # To get the proper end, we find the wordend of the character just before the cursor
            adj_end_pos = self.text_area.index(f"{self.text_area.index(f'{end_pos}-1c')} wordend")

            # If snapping resulted in an invalid range, abort.
            if self.text_area.compare(adj_start_pos, ">=", adj_end_pos):
                if needs_re_disable: self.text_area.config(state=tk.DISABLED)
                return

            final_text = self.text_area.get(adj_start_pos, adj_end_pos)
            if not final_text.strip(): # Ignore if selection is only whitespace
                if needs_re_disable: self.text_area.config(state=tk.DISABLED)
                return

            # --- End of new logic ---

            start_line, start_char = map(int, adj_start_pos.split('.'))
            end_line, end_char = map(int, adj_end_pos.split('.'))
            tag = self.selected_entity_tag.get()
            if not tag:
                messagebox.showwarning("Warning", "No entity tag selected.", parent=self.root)
                if needs_re_disable: self.text_area.config(state=tk.DISABLED)
                return

            entities_in_file = self.annotations.get(self.current_file_path, {}).get("entities", [])

            # Conditional overlap/duplicate checking (this logic is preserved)
            if not self.allow_multilabel_overlap.get():
                problematic_overlap_entity = None
                for existing_ann in entities_in_file:
                    if self._is_overlapping_in_list(start_line, start_char, end_line, end_char, [existing_ann]):
                        problematic_overlap_entity = existing_ann
                        break
                if problematic_overlap_entity:
                    messagebox.showwarning("Overlap Detected",
                        f"Proposed annotation '{final_text[:30]}...' overlaps with an existing one.\n\nEnable 'Allow Multi-label & Overlapping Annotations' in Settings to permit this.",
                        parent=self.root)
                    if needs_re_disable: self.text_area.config(state=tk.DISABLED)
                    return
            else:
                is_absolute_duplicate = False
                for existing_ann in entities_in_file:
                    if (existing_ann.get('start_line') == start_line and
                        existing_ann.get('start_char') == start_char and
                        existing_ann.get('end_line') == end_line and
                        existing_ann.get('end_char') == end_char and
                        existing_ann.get('tag') == tag):
                        is_absolute_duplicate = True
                        break
                if is_absolute_duplicate:
                    self.status_var.set(f"This exact annotation (span and tag '{tag}') already exists.")
                    if needs_re_disable: self.text_area.config(state=tk.DISABLED)
                    return

            # If all checks pass, proceed to add annotation
            file_data = self.annotations.setdefault(self.current_file_path, {"entities": [], "relations": []})
            entities_list = file_data.setdefault("entities", [])
            entity_id = uuid.uuid4().hex
            annotation = {'id': entity_id, 'start_line': start_line, 'start_char': start_char,
                          'end_line': end_line, 'end_char': end_char, 'text': final_text, 'tag': tag}
            entities_list.append(annotation)

            try:
                self.text_area.tag_remove(tk.SEL, "1.0", tk.END)
            except tk.TclError:
                pass

            self.apply_annotations_to_text()
            self.update_entities_list()
            self.root.update_idletasks()

            # Try to find and select the new annotation in the tree view
            try:
                new_tree_row_iid = None
                for tree_iid_candidate in self._entity_id_to_tree_iids.get(entity_id, []):
                    if self.entities_tree.exists(tree_iid_candidate):
                        item_values = self.entities_tree.item(tree_iid_candidate, 'values')
                        if (item_values and len(item_values) == 5 and
                            item_values[0] == entity_id and
                            item_values[1] == adj_start_pos and
                            item_values[2] == adj_end_pos and
                            item_values[4] == tag):
                            new_tree_row_iid = tree_iid_candidate
                            break
                if new_tree_row_iid:
                    self.entities_tree.selection_set(new_tree_row_iid)
                    self.entities_tree.focus(new_tree_row_iid)
                    self.entities_tree.see(new_tree_row_iid)
                    self.on_entity_select(None)
            except Exception as e:
                print(f"Error selecting new entity in list: {e}")

            self.status_var.set(f"Annotated: '{final_text[:30].replace(os.linesep, ' ')}...' as {tag}")
            self._update_button_states()

        except tk.TclError:
            # This can happen if no selection exists when the function is called
            pass
        except Exception as e:
            messagebox.showerror("Annotation Error", f"An unexpected error occurred during annotation:\n{e}", parent=self.root)
            traceback.print_exc()
        finally:
            # Restore original state if it was changed and widget exists
            if self.text_area.winfo_exists() and needs_re_disable:
                try: self.text_area.config(state=tk.DISABLED)
                except tk.TclError: pass

    def remove_entity_annotation(self, event=None):
        # If the function is already running, ignore this new call.
        if self._is_deleting:
            return

        self._is_deleting = True # Activate the lock
        try:
            # --- All of the original deletion logic is now inside this try block ---
            selected_tree_iids = self.entities_tree.selection()
            if not selected_tree_iids:
                messagebox.showinfo("Info", "Select one or more entities from the list to remove.", parent=self.root)
                return

            if not self.current_file_path or self.current_file_path not in self.annotations:
                messagebox.showerror("Error", "Cannot remove entity: No file/annotations.", parent=self.root)
                return

            entities_to_remove_data = []
            entity_ids_to_remove = set()
            entities_in_file = self.annotations.get(self.current_file_path, {}).get("entities", [])

            for tree_iid in selected_tree_iids:
                if not self.entities_tree.exists(tree_iid): continue
                try:
                    parts = tree_iid.split('|')
                    if len(parts) < 6 or parts[0] != 'entity': continue

                    entity_id, start_pos_str, end_pos_str, tag_from_tree = parts[1], parts[2], parts[3], parts[4]

                    for entity_dict in entities_in_file:
                        if (entity_dict.get('id') == entity_id and
                            f"{entity_dict.get('start_line')}.{entity_dict.get('start_char')}" == start_pos_str and
                            f"{entity_dict.get('end_line')}.{entity_dict.get('end_char')}" == end_pos_str and
                            entity_dict.get('tag') == tag_from_tree):
                            entities_to_remove_data.append(entity_dict)
                            entity_ids_to_remove.add(entity_id)
                            break
                except Exception as e:
                    print(f"Warning: Could not parse tree item IID '{tree_iid}': {e}")

            if not entities_to_remove_data:
                messagebox.showerror("Error", "Could not retrieve data for selected entities.", parent=self.root)
                return

            confirm = messagebox.askyesno("Confirm Removal",
                f"Remove {len(entities_to_remove_data)} selected entity instance(s)?\n"
                f"WARNING: If all instances of an entity ID are removed, associated relations will also be removed.", parent=self.root)

            if not confirm: return

            self.text_area.tag_remove("selection_highlight", "1.0", tk.END)

            temp_entities_list = entities_in_file[:]
            for entity_to_del in entities_to_remove_data:
                try:
                    temp_entities_list.remove(entity_to_del)
                except ValueError:
                    print(f"Warning: Entity to delete not found in list: {entity_to_del.get('id')}")

            self.annotations[self.current_file_path]["entities"] = temp_entities_list
            removed_entity_count = len(entities_to_remove_data)
            relations = self.annotations[self.current_file_path].get("relations", [])
            removed_relation_count = 0

            remaining_entity_ids_in_file = {e.get('id') for e in self.annotations[self.current_file_path]["entities"]}
            ids_that_became_orphaned = entity_ids_to_remove - remaining_entity_ids_in_file

            if relations and ids_that_became_orphaned:
                relations_original_count = len(relations)
                relations_remaining = [rel for rel in relations if
                                    rel.get('head_id') not in ids_that_became_orphaned and
                                    rel.get('tail_id') not in ids_that_became_orphaned]
                removed_relation_count = relations_original_count - len(relations_remaining)
                self.annotations[self.current_file_path]["relations"] = relations_remaining

            self.update_entities_list()
            self.update_relations_list()
            self.apply_annotations_to_text()
            self.status_var.set(f"Removed {removed_entity_count} entity instances. {removed_relation_count} relations potentially removed.")
            self._update_button_states()

        finally:
            self._is_deleting = False


    def merge_selected_entities(self):
        selected_tree_iids = self.entities_tree.selection()
        if len(selected_tree_iids) < 2:
            messagebox.showinfo("Info", "Select 2+ entity instances to merge.", parent=self.root); return
        if not self.current_file_path or self.current_file_path not in self.annotations:
            messagebox.showerror("Error", "Cannot merge: No file/annotations.", parent=self.root); return

        selected_entities_data = []
        entities_in_file = self.annotations.get(self.current_file_path, {}).get("entities", [])
        processed_tree_row_keys = set()

        for tree_iid in selected_tree_iids:
            if not self.entities_tree.exists(tree_iid): continue
            try:
                parts = tree_iid.split('|')
                if len(parts) < 6 or parts[0] != 'entity': continue

                entity_id = parts[1]
                start_pos_str = parts[2]
                end_pos_str = parts[3]
                tag_from_tree = parts[4]

                tree_row_key = (entity_id, start_pos_str, end_pos_str, tag_from_tree)
                if tree_row_key in processed_tree_row_keys: continue

                # Find the backing dictionary for this specific instance
                found_dict = None
                for entity_dict in entities_in_file:
                    if (entity_dict.get('id') == entity_id and
                        f"{entity_dict.get('start_line')}.{entity_dict.get('start_char')}" == start_pos_str and
                        f"{entity_dict.get('end_line')}.{entity_dict.get('end_char')}" == end_pos_str and
                        entity_dict.get('tag') == tag_from_tree):
                        found_dict = entity_dict
                        break

                if found_dict:
                    selected_entities_data.append(found_dict)
                    processed_tree_row_keys.add(tree_row_key)
                else:
                    print(f"Warning: Could not find backing data for tree row: {tree_row_key}")
            except Exception as e:
                print(f"Warning: Error getting data for merge: {e}")

        if len(selected_entities_data) < 2:
            messagebox.showerror("Error", "Need at least two valid and distinct instances to merge.", parent=self.root); return

        selected_entities_data.sort(key=lambda e: (e.get('start_line', 0), e.get('start_char', 0), e.get('id')))
        canonical_entity_dict = selected_entities_data[0]
        canonical_id = canonical_entity_dict.get('id')
        if not canonical_id: messagebox.showerror("Error", "Failed to get canonical ID.", parent=self.root); return

        ids_to_change_to_canonical = {e.get('id') for e in selected_entities_data if e.get('id') != canonical_id}
        dicts_to_update_id_field = [e for e in selected_entities_data if e.get('id') != canonical_id]

        if not dicts_to_update_id_field:
            messagebox.showinfo("Info", "Selected instances already share the same ID.", parent=self.root); return

        confirm = messagebox.askyesno("Confirm Merge",
            f"Merge {len(selected_entities_data)} selected instances to share the ID of the first selected instance ('{canonical_entity_dict.get('text', '')[:20]}...', ID: {canonical_id[:8]})?\n"
            f"The tags of individual instances will remain, but they will all point to this common ID.\n"
            f"Relations involving the old IDs will be updated to use the new common ID. Duplicate relations may be removed.", parent=self.root)
        if not confirm: self.status_var.set("Merge cancelled."); return

        modified_entity_instances = 0
        for entity_dict_instance in dicts_to_update_id_field:
            if entity_dict_instance['id'] != canonical_id:
                entity_dict_instance['id'] = canonical_id
                modified_entity_instances += 1

        modified_relation_endpoints = 0
        relations = self.annotations[self.current_file_path].get("relations", [])
        if relations and ids_to_change_to_canonical:
            for i, rel in enumerate(relations):
                rel_mod = False
                if rel.get('head_id') in ids_to_change_to_canonical:
                    relations[i]['head_id'] = canonical_id
                    rel_mod = True
                if rel.get('tail_id') in ids_to_change_to_canonical:
                    relations[i]['tail_id'] = canonical_id
                    rel_mod = True
                if rel_mod: modified_relation_endpoints += 1

        removed_duplicates = 0
        if relations and modified_relation_endpoints > 0:
            unique_relations = []; seen_signatures = set()
            for rel in relations:
                sig = (rel.get('head_id'), rel.get('tail_id'), rel.get('type'))
                if sig not in seen_signatures:
                    seen_signatures.add(sig); unique_relations.append(rel)
                else: removed_duplicates += 1
            if removed_duplicates > 0:
                self.annotations[self.current_file_path]["relations"] = unique_relations

        self.update_entities_list(); self.update_relations_list(); self.apply_annotations_to_text()
        self.root.update_idletasks()

        tree_iids_to_reselect_after_merge = []
        try:
            if canonical_id in self._entity_id_to_tree_iids:
                tree_iids_to_reselect_after_merge = self._entity_id_to_tree_iids[canonical_id]
            if tree_iids_to_reselect_after_merge:
                valid_reselect = [tid for tid in tree_iids_to_reselect_after_merge if self.entities_tree.exists(tid)]
                if valid_reselect:
                    self.entities_tree.selection_set(valid_reselect)
                    if valid_reselect:
                        self.entities_tree.focus(valid_reselect[0])
                        self.entities_tree.see(valid_reselect[0])
                    self.on_entity_select(None)
                else: self.selected_entity_ids_for_relation = []; self._update_button_states()
            else: self.selected_entity_ids_for_relation = []; self._update_button_states()
        except Exception as e:
            print(f"Warning: Error re-selecting merged entities: {e}")
            self.selected_entity_ids_for_relation = []; self._update_button_states()

        status_msg = f"Merged. {modified_entity_instances} instances now share ID '{canonical_id[:8]}...'. Updated {modified_relation_endpoints} relation endpoints."
        if removed_duplicates > 0: status_msg += f" Removed {removed_duplicates} duplicate relations."
        self.status_var.set(status_msg)


    def _on_text_right_click(self, event):
        if not self.current_file_path: return
        try:
            click_index_str = self.text_area.index(f"@{event.x},{event.y}")
            click_line, click_char = map(int, click_index_str.split('.'))
        except tk.TclError: return
        clicked_entity_dict = None
        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        # Find the specific entity instance clicked on
        # Iterate reversed to get the "topmost" if multiple annotations overlap at the click point
        for entity in reversed(entities):
            start_l, start_c = entity.get('start_line'), entity.get('start_char')
            end_l, end_c = entity.get('end_line'), entity.get('end_char')
            if start_l is None or start_c is None or end_l is None or end_c is None: continue
            span_start = (start_l, start_c); span_end = (end_l, end_c)
            click_pos = (click_line, click_char)
            if span_start <= click_pos < span_end:
                clicked_entity_dict = entity; break # Found the one to act on
        if not clicked_entity_dict: return

        entity_id = clicked_entity_dict.get('id')
        is_part_of_merged_set = False # Does this instance share its ID with other instances?
        if entity_id:
            count = sum(1 for e in entities if e.get('id') == entity_id)
            if count > 1: is_part_of_merged_set = True

        context_menu = tk.Menu(self.root, tearoff=0)
        # Demerge is only enabled if this instance is part of a set of instances sharing an ID
        demerge_state = tk.NORMAL if is_part_of_merged_set else tk.DISABLED
        context_menu.add_command(label="Demerge This Instance (Assign New ID)", state=demerge_state,
                                 command=lambda e=clicked_entity_dict: self.demerge_entity(e))
        context_menu.add_separator()
        status_text = "Part of Merged Set" if is_part_of_merged_set else "Unique ID Instance"
        context_menu.add_command(label=f"ID: {entity_id[:8]}... ({status_text})", state=tk.DISABLED)
        context_menu.add_command(label=f"Tag: {clicked_entity_dict.get('tag', 'N/A')}", state=tk.DISABLED)
        propagated_status = "Propagated" if clicked_entity_dict.get('propagated', False) else "Manual"
        context_menu.add_command(label=f"Origin: {propagated_status}", state=tk.DISABLED)
        try: context_menu.tk_popup(event.x_root, event.y_root)
        finally: context_menu.grab_release()


    def demerge_entity(self, entity_dict_to_demerge):
        if not self.current_file_path: return
        file_data = self.annotations.get(self.current_file_path)
        if not file_data or "entities" not in file_data: return
        entities_list = file_data["entities"] # This is a direct reference

        # Find the exact dictionary instance in the entities_list
        found_entity_instance = None
        for i, entity_instance in enumerate(entities_list):
            # Compare by object identity if possible, or by all relevant fields
            if entity_instance is entity_dict_to_demerge:
                 found_entity_instance = entity_instance
                 break

        if not found_entity_instance: # Fallback if direct object match failed (should not happen if passed correctly)
            for i, entity_instance in enumerate(entities_list):
                if (entity_instance.get('id') == entity_dict_to_demerge.get('id') and
                    entity_instance.get('start_line') == entity_dict_to_demerge.get('start_line') and
                    entity_instance.get('start_char') == entity_dict_to_demerge.get('start_char') and
                    entity_instance.get('end_line') == entity_dict_to_demerge.get('end_line') and
                    entity_instance.get('end_char') == entity_dict_to_demerge.get('end_char') and
                    entity_instance.get('tag') == entity_dict_to_demerge.get('tag') ): # Match all to be sure
                    found_entity_instance = entity_instance
                    break

        if not found_entity_instance:
            messagebox.showerror("Error", "Could not find the exact entity instance to demerge.", parent=self.root); return

        # Assign a new unique ID to this specific instance
        new_id = uuid.uuid4().hex
        found_entity_instance['id'] = new_id # Modify the dict in-place

        self.update_entities_list(); self.apply_annotations_to_text(); self.update_relations_list()
        demerged_text = found_entity_instance.get('text', '')[:30]
        self.status_var.set(f"Demerged instance '{demerged_text}...'. New ID: {new_id[:8]}...")
        self._update_button_states()

        # Try to select the newly demerged entity in the list
        try:
            self.root.update_idletasks()
            new_tree_row_iid = None
            # Search the treeview for the item with the new ID AND correct original position & tag
            for tree_iid in self.entities_tree.get_children(""):
                row_values = self.entities_tree.item(tree_iid, 'values')
                if row_values and len(row_values) == 5 and row_values[0] == new_id:
                    # Check position and tag to ensure we select the correct instance just demerged
                    if (f"{found_entity_instance['start_line']}.{found_entity_instance['start_char']}" == row_values[1] and
                        f"{found_entity_instance['end_line']}.{found_entity_instance['end_char']}" == row_values[2] and
                        found_entity_instance['tag'] == row_values[4]):
                        new_tree_row_iid = tree_iid; break
            if new_tree_row_iid and self.entities_tree.exists(new_tree_row_iid):
                self.entities_tree.selection_set(new_tree_row_iid)
                self.entities_tree.focus(new_tree_row_iid)
                self.entities_tree.see(new_tree_row_iid)
                self.on_entity_select(None)
            else: print(f"Warning: Could not select demerged entity (ID: {new_id[:8]}) in the list.")
        except Exception as e: print(f"Warning: Could not select demerged entity in the list: {e}")


    def apply_annotations_to_text(self):
        if not self.current_file_path: return
        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL)
        try:
            current_text_tags = list(self.text_area.tag_names())
            tags_to_remove = set(self.entity_tags)
            tags_to_remove.add("propagated_entity")
            for tag_name in current_text_tags:
                if tag_name in tags_to_remove and tag_name != tk.SEL:
                    try: self.text_area.tag_remove(tag_name, "1.0", tk.END)
                    except tk.TclError: pass
            entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
            # Sort by start position, then by end position (shorter ones first if start is same)
            # This helps with visual layering if desired, though Tkinter's last-applied tag "wins" for bg.
            sorted_entities = sorted(entities, key=lambda a: (
                a.get('start_line', 0), a.get('start_char', 0),
                -a.get('end_line', 0), -a.get('end_char', 0) # Shorter spans drawn first for same start
            ))
            for ann in sorted_entities:
                try:
                    start_pos = f"{ann['start_line']}.{ann['start_char']}"
                    end_pos = f"{ann['end_line']}.{ann['end_char']}"
                    tag = ann.get('tag'); is_propagated = ann.get('propagated', False)
                    if tag and tag in self.entity_tags: # Only apply known tags
                        # Ensure tag is configured (it should be if in self.entity_tags)
                        if tag not in self.text_area.tag_names(): self._configure_text_tags() # Reconfigure if somehow missing

                        if tag in self.text_area.tag_names(): # Check again
                            self.text_area.tag_raise(tag)
                            self.text_area.tag_add(tag, start_pos, end_pos)
                            if is_propagated:
                                try:
                                    # Ensure propagated tag is configured
                                    if "propagated_entity" not in self.text_area.tag_names():
                                        self.text_area.tag_configure("propagated_entity", underline=True)
                                    self.text_area.tag_add("propagated_entity", start_pos, end_pos)
                                except tk.TclError as e: print(f"Warn: Underline fail for '{tag}': {e}")
                        else: print(f"Warn: Tag '{tag}' unconfigurable in text area for entity ID {ann.get('id','N/A')}.")
                    elif tag: print(f"Warn: Unknown entity tag '{tag}' encountered during highlight for entity ID {ann.get('id','N/A')}.")
                except KeyError as e: print(f"Warn: Highlight fail, missing key {e}: Entity ID {ann.get('id','N/A')}")
                except tk.TclError as e: print(f"Warn: TclError applying highlight for '{start_pos}'-'{end_pos}': {e}: Entity ID {ann.get('id','N/A')}")
                except Exception as e: print(f"Warn: General highlight fail: {e}: Entity ID {ann.get('id','N/A')}")
        finally:
            if self.text_area.winfo_exists():
                self.text_area.config(state=original_state)


    def update_entities_list(self):
        selected_data_keys = set()
        selected_tree_iids_before_update = self.entities_tree.selection()
        for tree_iid in selected_tree_iids_before_update:
            if not self.entities_tree.exists(tree_iid): continue
            try:
                vals = self.entities_tree.item(tree_iid, 'values')
                # Key: (id, start_pos_str, end_pos_str, tag) - to uniquely identify what was selected
                if vals and len(vals) == 5:
                    selected_data_keys.add( (vals[0], vals[1], vals[2], vals[4]) )
            except Exception: pass

        try: self.entities_tree.delete(*self.entities_tree.get_children())
        except Exception: pass
        self._entity_id_to_tree_iids = {} # Reset mapping

        if not self.current_file_path: self._update_button_states(); return
        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        if not entities: self.selected_entity_ids_for_relation = []; self._update_button_states(); return

        # Sort entities for display in the list
        sorted_entities = sorted(entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0), a.get('id', ''), a.get('tag', '')))

        entity_id_counts = {} # Count occurrences of each conceptual entity ID
        for ann in sorted_entities:
            eid = ann.get('id');
            if eid: entity_id_counts[eid] = entity_id_counts.get(eid, 0) + 1

        tree_iids_to_restore_selection = []
        for ann_index, ann in enumerate(sorted_entities): # ann_index helps ensure unique iid
            entity_id = ann.get('id');
            if not entity_id: print(f"Warning: Entity missing ID: {ann}"); continue # Skip if somehow an entity lacks an ID
            try:
                sl, sc = ann['start_line'], ann['start_char']; el, ec = ann['end_line'], ann['end_char']
                start_pos_str, end_pos_str = f"{sl}.{sc}", f"{el}.{ec}"
                full_text = ann.get('text', '')
                disp_text = full_text.replace(os.linesep,' ').replace('\n', ' ').replace('\r', ' ')[:60] + ("..." if len(full_text)>60 else "")
                tag = ann.get('tag', 'N/A')

                # Apply 'merged' visual tag if this conceptual entity ID appears for multiple instances/spans/tags
                tree_tags_tuple = ('merged',) if entity_id_counts.get(entity_id, 0) > 1 else ()

                # Generate a unique iid for this specific annotation instance in the tree
                # Include tag in iid to differentiate if same span has multiple tags (different annotations)
                tree_row_iid = f"entity|{entity_id}|{start_pos_str}|{end_pos_str}|{tag}|{ann_index}"

                values_tuple = (entity_id, start_pos_str, end_pos_str, disp_text, tag)

                self.entities_tree.insert("", tk.END, iid=tree_row_iid, values=values_tuple, tags=tree_tags_tuple)

                if entity_id not in self._entity_id_to_tree_iids: self._entity_id_to_tree_iids[entity_id] = []
                self._entity_id_to_tree_iids[entity_id].append(tree_row_iid)

                # Check if this entity instance (id, span, tag) was previously selected
                current_data_key = (entity_id, start_pos_str, end_pos_str, tag)
                if current_data_key in selected_data_keys:
                    tree_iids_to_restore_selection.append(tree_row_iid)
            except KeyError as e: print(f"Error adding entity to list (KeyError): {e} in {ann}")
            except Exception as e: print(f"Error adding entity to list (Exception): {e} in {ann}")

        # Restore selection
        if tree_iids_to_restore_selection:
            try:
                valid_restore = [tid for tid in tree_iids_to_restore_selection if self.entities_tree.exists(tid)]
                if valid_restore:
                    self.entities_tree.selection_set(valid_restore)
                    self.entities_tree.focus(valid_restore[0]) # Focus first selected
                    self.entities_tree.see(valid_restore[0]) # Scroll to first selected
                self.on_entity_select(None) # Update internal state based on new selection (even if empty)
            except Exception as e:
                print(f"Warning: Could not restore selection: {e}")
                self.selected_entity_ids_for_relation = [] # Clear on error
        else: # If nothing was selected or nothing to restore
            self.selected_entity_ids_for_relation = []
            self.on_entity_select(None) # Still call to ensure button states are correct for empty selection

        self._update_button_states() # Update buttons based on current selection state


    def on_entity_select(self, event):
        selected_tree_iids = self.entities_tree.selection()
        self.selected_entity_ids_for_relation = [] # This stores UNIQUE entity IDs
        unique_entity_ids_in_current_selection = set()

        for tree_iid in selected_tree_iids:
            if not self.entities_tree.exists(tree_iid): continue
            try:
                values = self.entities_tree.item(tree_iid, 'values')
                if values and len(values) > 0: # values[0] is the entity_id
                    actual_entity_id = values[0]
                    if actual_entity_id and actual_entity_id not in unique_entity_ids_in_current_selection:
                        self.selected_entity_ids_for_relation.append(actual_entity_id)
                        unique_entity_ids_in_current_selection.add(actual_entity_id)
            except Exception as e: print(f"Warning: Could not get entity ID from selection: {e}")

        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL) # Must be normal to add tags
        try:
            # This line is now corrected to remove the custom highlight
            self.text_area.tag_remove("selection_highlight", "1.0", tk.END)

            first_entity_pos_to_see = None

            # Highlight all selected spans in the text_area
            for tree_iid in selected_tree_iids:
                if not self.entities_tree.exists(tree_iid): continue
                try:
                    values = self.entities_tree.item(tree_iid, 'values')
                    # values are (entity_id, start_pos_str, end_pos_str, disp_text, tag)
                    if values and len(values) >= 3:
                        start_pos_str, end_pos_str = values[1], values[2]
                        try:
                            # This adds to the text widget's own selection highlight
                            self.text_area.tag_add("selection_highlight", start_pos_str, end_pos_str)
                            if first_entity_pos_to_see is None: first_entity_pos_to_see = start_pos_str
                        except tk.TclError as te: print(f"Warning: Error highlighting entity span from list: {te}")
                except Exception as e: print(f"Warning: Error processing entity selection for text highlight: {e}")

            if first_entity_pos_to_see: # Scroll to the first span in the selection
                try: self.text_area.see(first_entity_pos_to_see)
                except tk.TclError as e: print(f"Warning: Error scrolling to selected entity: {e}")
        finally:
            if self.text_area.winfo_exists():
                self.text_area.config(state=original_state) # Restore original state
        self._update_button_states()


    def add_relation(self):
        if len(self.selected_entity_ids_for_relation) != 2:
            messagebox.showerror("Selection Error", "Select exactly TWO entities (representing two unique entity IDs) from the list (Head first, then Tail).", parent=self.root)
            return
        head_id, tail_id = self.selected_entity_ids_for_relation[0], self.selected_entity_ids_for_relation[1]
        relation_type = self.selected_relation_type.get()
        if not relation_type:
            messagebox.showerror("Selection Error", "Select a relation type.", parent=self.root)
            return
        if not self.current_file_path or self.current_file_path not in self.annotations:
            messagebox.showerror("Error", "Cannot add relation: No file/annotations.", parent=self.root)
            return
        file_data = self.annotations.setdefault(self.current_file_path, {"entities": [], "relations": []})
        relations_list = file_data.setdefault("relations", [])
        if any(r.get('head_id') == head_id and r.get('tail_id') == tail_id and r.get('type') == relation_type for r in relations_list):
            messagebox.showwarning("Duplicate Relation", "This exact relation (same Head ID, Tail ID, and Type) already exists.", parent=self.root)
            return
        relation_id = uuid.uuid4().hex
        new_relation = {"id": relation_id, "type": relation_type, "head_id": head_id, "tail_id": tail_id}
        relations_list.append(new_relation)
        self.update_relations_list()
        self.root.update_idletasks()
        try:
            if self.relations_tree.exists(relation_id):
                self.relations_tree.selection_set(relation_id)
                self.relations_tree.focus(relation_id)
                self.relations_tree.see(relation_id)
                self.on_relation_select(None)
            else: print(f"Warning: Could not find new relation {relation_id} in tree.")
        except Exception as e: print(f"Error selecting new relation: {e}")
        self.status_var.set(f"Added Relation: {relation_type} ({head_id[:4]}... -> {tail_id[:4]}...)")


    def flip_selected_relation(self):
        selected_iids = self.relations_tree.selection()
        if len(selected_iids) != 1: return
        relation_id_to_flip = selected_iids[0]
        relations = self.annotations.get(self.current_file_path, {}).get("relations")
        if not relations: return
        found = False
        flipped_relation_index = -1
        for i, rel in enumerate(relations):
            if rel.get('id') == relation_id_to_flip:
                current_head, current_tail = rel.get('head_id'), rel.get('tail_id')
                current_type = rel.get('type')
                if current_head and current_tail and current_type:
                    if any(r.get('head_id') == current_tail and r.get('tail_id') == current_head and r.get('type') == current_type
                           for r_idx, r in enumerate(relations) if i != r_idx):
                        messagebox.showwarning("Duplicate Relation", "Flipping this relation would create a duplicate of an existing relation.", parent=self.root)
                        return
                    relations[i]['head_id'], relations[i]['tail_id'] = current_tail, current_head
                    found = True
                    flipped_relation_index = i
                    break
                else:
                    messagebox.showerror("Data Error", "Selected relation missing Head/Tail ID or Type.", parent=self.root)
                    return
        if found:
            self.update_relations_list()
            self.root.update_idletasks()
            try:
                if self.relations_tree.exists(relation_id_to_flip):
                    self.relations_tree.selection_set(relation_id_to_flip)
                    self.relations_tree.focus(relation_id_to_flip)
                    self.relations_tree.see(relation_id_to_flip)
                    self.on_relation_select(None)
            except Exception as e: print(f"Warning: Error re-selecting flipped relation: {e}")
            self.status_var.set("Relation Head/Tail flipped.")


    def remove_relation_annotation(self, event=None):
        selected_iids = self.relations_tree.selection()
        if len(selected_iids) != 1: return
        relation_id_to_remove = selected_iids[0]
        relations = self.annotations.get(self.current_file_path, {}).get("relations")
        if not relations: return
        original_length = len(relations)
        self.annotations[self.current_file_path]["relations"] = [
            rel for rel in relations if rel.get('id') != relation_id_to_remove
        ]
        if len(self.annotations[self.current_file_path]["relations"]) < original_length:
            self.update_relations_list()
            self.status_var.set("Relation removed.")
            self._update_button_states()
        else:
            messagebox.showwarning("Not Found", "Could not find the selected relation to remove.", parent=self.root)


    def update_relations_list(self):
        selected_rel_iids = self.relations_tree.selection()
        try: self.relations_tree.delete(*self.relations_tree.get_children())
        except Exception: pass
        if not self.current_file_path: self._update_button_states(); return
        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        relations = self.annotations.get(self.current_file_path, {}).get("relations", [])
        if not relations: self._update_button_states(); return
        entity_display_map = {}
        processed_ids_for_map = set()
        # Sort entities by position to get the 'first' one consistently if merged
        # (though for relations, any instance's text for that ID is usually fine)
        sorted_entities_for_map = sorted(entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0), a.get('tag','')))
        for entity in sorted_entities_for_map:
            eid = entity.get('id')
            if eid and eid not in processed_ids_for_map:
                etext = entity.get('text', 'N/A')
                etag = entity.get('tag', 'N/A')
                # Make display text more informative by including the tag
                disp_text = etext.replace(os.linesep,' ').replace('\n', ' ').replace('\r', ' ')[:25] + ("..." if len(etext)>25 else "")
                entity_display_map[eid] = f"{disp_text} ({etag})"
                processed_ids_for_map.add(eid)

        sorted_relations = sorted(relations, key=lambda r: (r.get('type', ''), r.get('head_id',''), r.get('tail_id','')))
        for rel in sorted_relations:
            rel_id, head_id, tail_id, rel_type = rel.get('id'), rel.get('head_id'), rel.get('tail_id'), rel.get('type')
            if not (rel_id and head_id and tail_id and rel_type): continue
            head_text = entity_display_map.get(head_id, f"<ID: {head_id[:6]}...>")
            tail_text = entity_display_map.get(tail_id, f"<ID: {tail_id[:6]}...>")
            values = (rel_id, head_text, rel_type, tail_text)
            try:
                self.relations_tree.insert("", tk.END, iid=rel_id, values=values)
            except Exception as e: print(f"Error inserting relation {rel_id} into tree: {e}")
        valid_selection = [rid for rid in selected_rel_iids if self.relations_tree.exists(rid)]
        if valid_selection:
            try:
                self.relations_tree.selection_set(valid_selection)
                self.relations_tree.focus(valid_selection[0])
                self.relations_tree.see(valid_selection[0])
            except Exception as e: print(f"Warning: Could not restore relation selection: {e}")
        self._update_button_states()


    def on_relation_select(self, event):
        self._update_button_states()


    def propagate_annotations(self):
        if not self.current_file_path or not self.files_list:
            messagebox.showinfo("Info", "Load a directory first.", parent=self.root); return
        source_entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        if not source_entities:
            messagebox.showinfo("Info", "No entities in current file to propagate.", parent=self.root); return
        text_to_tag = {}
        processed_texts = set()
        sorted_source = sorted(source_entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0)))
        for ann in sorted_source:
            text = ann.get('text','').strip()
            tag = ann.get('tag')
            if text and tag and text not in processed_texts: # Use first encountered tag for a given text
                text_to_tag[text] = tag
                processed_texts.add(text)
        if not text_to_tag:
            messagebox.showinfo("Info", "No valid text/tag pairs found in current file to propagate.", parent=self.root); return
        confirm_msg = (f"Search for {len(text_to_tag)} unique text/tag pairs from '{os.path.basename(self.current_file_path)}' "
                       f"across all {len(self.files_list)} files?\n\n"
                       f"WARNING: Adds new entities (underlined, whitespace stripped). ")
        if self.allow_multilabel_overlap.get():
            confirm_msg += "Overlaps are allowed, but exact duplicates (span, text, tag) will be skipped. "
        else:
            confirm_msg += "Skips overlaps. "
        confirm_msg += "Relations not propagated."

        if not messagebox.askyesno("Confirm Propagation (Current File)", confirm_msg, parent=self.root):
            self.status_var.set("Propagation cancelled."); return
        self._perform_propagation(text_to_tag, "Current File Propagation")


    def load_and_propagate_from_dictionary(self):
        if not self.files_list: messagebox.showerror("Error", "Open a directory first.", parent=self.root); return
        if not self.entity_tags: messagebox.showwarning("Warning", "No entity tags defined.", parent=self.root); return

        dict_path = filedialog.askopenfilename(
            title="Select Dictionary File (Text<TAB/SPACE>Tag per line)",
            filetypes=[("Text files", "*.txt"), ("TSV files", "*.tsv"), ("All files", "*.*")], parent=self.root)
        if not dict_path: return

        dictionary_mapping = {}; lines_read, skipped_lines = 0, 0
        invalid_tags_found = set(); duplicate_texts = 0
        try:
            with open(dict_path, 'r', encoding='utf-8') as f:
                for line_num, line in enumerate(f, 1):
                    lines_read += 1; line = line.strip()
                    if not line or line.startswith('#'): skipped_lines +=1; continue
                    parts = line.split('\t')
                    if len(parts) != 2: parts = line.rsplit(maxsplit=1)
                    if len(parts) != 2: print(f"Warn: Bad dict line {line_num}: '{line}'"); skipped_lines += 1; continue

                    entity_text, label = parts[0].strip(), parts[1].strip()
                    if not entity_text: skipped_lines += 1; continue
                    if label not in self.entity_tags: invalid_tags_found.add(label); skipped_lines += 1; continue
                    if entity_text in dictionary_mapping and dictionary_mapping[entity_text] != label:
                        print(f"Warn: Duplicate text '{entity_text}' in dict line {line_num}. Overwriting tag '{dictionary_mapping[entity_text]}' with '{label}'.")
                        duplicate_texts += 1
                    dictionary_mapping[entity_text] = label
        except Exception as e: messagebox.showerror("Dict Read Error", f"Failed:\n{e}", parent=self.root); return

        valid_entries = len(dictionary_mapping)
        if not dictionary_mapping:
            msg = f"Dict '{os.path.basename(dict_path)}': Read {lines_read} lines, 0 valid entries.\n"
            if invalid_tags_found: msg += f"Skipped tags: {', '.join(list(invalid_tags_found)[:5])}...\n"
            messagebox.showinfo("Dictionary Results", msg, parent=self.root); return

        confirm_msg = f"Dict '{os.path.basename(dict_path)}' loaded.\n"
        confirm_msg += f"- {valid_entries} unique entries with valid tags.\n"
        confirm_msg += f"- {lines_read} lines read ({skipped_lines} skipped, {duplicate_texts} duplicates overwritten).\n"
        if invalid_tags_found: confirm_msg += f"- Skipped tags: {', '.join(list(invalid_tags_found)[:5])}...\n"
        confirm_msg += f"\nPropagate across {len(self.files_list)} files?\n\n(Adds entities (underlined, stripped). "
        if self.allow_multilabel_overlap.get():
            confirm_msg += "Overlaps are allowed, but exact duplicates (span, text, tag) will be skipped.)"
        else:
            confirm_msg += "Skips overlaps.)"


        if not messagebox.askyesno("Confirm Dictionary Propagation", confirm_msg, parent=self.root):
            self.status_var.set("Dictionary propagation cancelled."); return
        self._perform_propagation(dictionary_mapping, "Dictionary Propagation")


    def _perform_propagation(self, text_to_tag_map, source_description):
        propagated_count = 0; affected_files_count = 0
        extend_option = self.extend_to_word.get(); current_file_was_modified = False
        allow_overlap_setting = self.allow_multilabel_overlap.get()

        self.status_var.set(f"Starting {source_description}..."); self.root.update_idletasks()
        sorted_texts_to_find = sorted(text_to_tag_map.keys(), key=len, reverse=True)
        temp_text_widget = tk.Text()
        try:
            for i, file_path in enumerate(self.files_list):
                file_modified_in_this_run = False
                if (i + 1) % 10 == 0 or i == len(self.files_list) - 1:
                    self.status_var.set(f"{source_description}: Processing {i+1}/{len(self.files_list)}..."); self.root.update_idletasks()
                if not os.path.isfile(file_path):
                    print(f"Info: Skipping missing file during propagation: {file_path}"); continue
                try:
                    with open(file_path, 'r', encoding='utf-8') as f: content = f.read()
                    temp_text_widget.delete('1.0', tk.END)
                    temp_text_widget.insert('1.0', content)
                    file_data = self.annotations.setdefault(file_path, {"entities": [], "relations": []})
                    target_entities_list = file_data.setdefault("entities", [])
                    existing_entity_dicts_for_overlap_check = [e.copy() for e in target_entities_list]
                    newly_added_this_file_for_overlap_check = []
                    for text_to_find in sorted_texts_to_find:
                        tag_to_apply = text_to_tag_map[text_to_find]
                        if not text_to_find: continue
                        start_index = "1.0"
                        while True:
                            found_pos_str = temp_text_widget.search(text_to_find, start_index, stopindex=tk.END, exact=True, nocase=False)
                            if not found_pos_str: break
                            # Validate that the match is a whole word
                            is_start_boundary = (found_pos_str == "1.0") or \
                                (not temp_text_widget.get(f"{found_pos_str}-1c").isalnum())

                            end_of_match_idx = temp_text_widget.index(f"{found_pos_str}+{len(text_to_find)}c")
                            is_end_boundary = False
                            try:
                                is_end_boundary = not temp_text_widget.get(end_of_match_idx).isalnum()
                            except tk.TclError:
                                is_end_boundary = True # End of text is a valid boundary

                            # If not a whole word, skip to the next search
                            if not (is_start_boundary and is_end_boundary):
                                start_index = temp_text_widget.index(f"{found_pos_str}+1c")
                                continue
                            initial_end_pos_str = temp_text_widget.index(f"{found_pos_str}+{len(text_to_find)}c")
                            current_match_start_pos, current_match_end_pos = found_pos_str, initial_end_pos_str
                            if extend_option:
                                try:
                                    word_start_abs = temp_text_widget.index(f"{current_match_start_pos} wordstart")
                                    word_end_abs = temp_text_widget.index(f"{temp_text_widget.index(f'{current_match_end_pos}-1c')} wordend")
                                    if temp_text_widget.compare(word_start_abs, "<=", current_match_start_pos) and \
                                       temp_text_widget.compare(word_end_abs, ">=", current_match_end_pos) and \
                                       temp_text_widget.compare(word_start_abs, "<", word_end_abs):
                                        current_match_start_pos, current_match_end_pos = word_start_abs, word_end_abs
                                except tk.TclError: pass
                                except Exception as e: print(f"Warn: Word extension fail near {found_pos_str} in {os.path.basename(file_path)}: {e}")

                            span_text = temp_text_widget.get(current_match_start_pos, current_match_end_pos)
                            stripped_text = span_text.strip()
                            if not stripped_text:
                                start_index = initial_end_pos_str
                                continue
                            leading_ws = len(span_text) - len(span_text.lstrip())
                            adj_start_pos_str = temp_text_widget.index(f"{current_match_start_pos}+{leading_ws}c")
                            adj_end_pos_str = temp_text_widget.index(f"{adj_start_pos_str}+{len(stripped_text)}c")
                            try:
                                adj_sl, adj_sc = map(int, adj_start_pos_str.split('.'))
                                adj_el, adj_ec = map(int, adj_end_pos_str.split('.'))
                            except ValueError:
                                print(f"Error parsing adjusted positions during propagation: {adj_start_pos_str}/{adj_end_pos_str} in {os.path.basename(file_path)}")
                                start_index = initial_end_pos_str
                                continue
                            can_add_propagated_entity = True
                            all_relevant_entities_for_check = existing_entity_dicts_for_overlap_check + newly_added_this_file_for_overlap_check
                            if not allow_overlap_setting:
                                if self._is_overlapping_in_list(adj_sl, adj_sc, adj_el, adj_ec, all_relevant_entities_for_check):
                                    can_add_propagated_entity = False
                            else:
                                for existing_ann in all_relevant_entities_for_check:
                                    if (existing_ann.get('start_line') == adj_sl and
                                        existing_ann.get('start_char') == adj_sc and
                                        existing_ann.get('end_line') == adj_el and
                                        existing_ann.get('end_char') == adj_ec and
                                        existing_ann.get('text') == stripped_text and
                                        existing_ann.get('tag') == tag_to_apply):
                                        can_add_propagated_entity = False
                                        break
                            if can_add_propagated_entity:
                                entity_id = uuid.uuid4().hex
                                new_annotation = {'id': entity_id, 'start_line': adj_sl, 'start_char': adj_sc,
                                                  'end_line': adj_el, 'end_char': adj_ec, 'text': stripped_text,
                                                  'tag': tag_to_apply, 'propagated': True}
                                target_entities_list.append(new_annotation)
                                newly_added_this_file_for_overlap_check.append(new_annotation)
                                propagated_count += 1
                                file_modified_in_this_run = True
                                if file_path == self.current_file_path: current_file_was_modified = True
                            start_index = initial_end_pos_str
                except Exception as e: print(f"ERROR processing '{os.path.basename(file_path)}' during propagation:\n{str(e)}\n{traceback.format_exc()}")
                if file_modified_in_this_run: affected_files_count += 1
        finally:
            temp_text_widget.destroy()

        if current_file_was_modified:
            self.update_entities_list()
            self.apply_annotations_to_text()
        self._update_button_states()
        summary = f"{source_description} complete.\nAdded {propagated_count} entities across {affected_files_count} files."
        if extend_option: summary += "\n('Extend to whole word' was enabled)"
        if allow_overlap_setting: summary += "\n(Multi-label/overlap was enabled)"
        messagebox.showinfo("Propagation Results", summary, parent=self.root)
        self.status_var.set(f"{source_description} finished. Added {propagated_count} entities.")


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
            # Add hotkey numbers 1-9, 0 to the first 10 entity tags
            if item_type_name == "Entity Tags" and index < 10:
                hotkey_num = (index + 1) % 10
                display_text = f"{hotkey_num}: {item}"

            listbox.insert(tk.END, display_text) #

            if item_type_name == "Entity Tags":
                try:
                    # Use index instead of tk.END for accuracy
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
                existing = [listbox.get(i).lower() for i in range(listbox.size())]
                if item.lower() not in existing:
                    listbox.insert(tk.END, item)
                    items = list(listbox.get(0, tk.END)); items.sort(key=str.lower)
                    listbox.delete(0, tk.END)
                    for i_val in items:
                        listbox.insert(tk.END, i_val)
                        if item_type_name == "Entity Tags":
                            try: listbox.itemconfig(listbox.size() -1 , {'bg': self.get_color_for_tag(i_val)}) # itemconfig last item
                            except tk.TclError: pass
                    item_var.set(""); listbox.see(tk.END)
                else: messagebox.showwarning("Duplicate", f"'{item}' already exists.", parent=window)
            item_entry.focus_set()
        item_entry.bind("<Return>", lambda event: add_item())
        add_btn = tk.Button(controls_frame, text="Add", width=7, command=add_item)
        add_btn.grid(row=0, column=1, padx=5)
        def remove_item():
            indices = listbox.curselection()
            if indices:
                items_to_remove = [listbox.get(i) for i in indices]
                if item_type_name == "Entity Tags":
                    tags_in_use = set()
                    for data in self.annotations.values():
                        for entity in data.get("entities", []):
                            if entity.get('tag') in items_to_remove:
                                tags_in_use.add(entity.get('tag'))
                    if tags_in_use:
                        if not messagebox.askyesno("Confirm Tag Removal",
                            f"The following tags are used by existing annotations:\n- {', '.join(tags_in_use)}\n\nRemove anyway? (Annotations will lose their tag and color)", parent=window): return
                for index in sorted(indices, reverse=True):
                    listbox.delete(index)
            else: messagebox.showwarning("No Selection", "Select item(s) to remove.", parent=window)
        remove_btn = tk.Button(controls_frame, text="Remove", width=7, command=remove_item)
        remove_btn.grid(row=0, column=2)
        button_frame = tk.Frame(window); button_frame.pack(fill=tk.X, padx=10, pady=(5, 10))
        def save_changes():
            new_items = list(listbox.get(0, tk.END))
            if item_type_name == "Entity Tags":
                # Strip the "1: " prefix before saving
                new_items = [re.sub(r"^\d:\s", "", item) for item in new_items]
            if set(new_items) != set(current_items_list):
                removed = set(current_items_list) - set(new_items)
                added = set(new_items) - set(current_items_list)
                current_items_list[:] = new_items
                update_combobox_func()
                if item_type_name == "Entity Tags":
                    for tag_val in added: self.get_color_for_tag(tag_val)
                    self._configure_text_tags()
                    for tag_val in removed:
                        try: self.text_area.tag_delete(tag_val)
                        except tk.TclError: pass
                        if tag_val in self.tag_colors: del self.tag_colors[tag_val]
                    self.apply_annotations_to_text(); self.update_entities_list()
                elif item_type_name == "Relation Types": self.update_relations_list()
                self.status_var.set(f"{item_type_name} updated.")
            else:
                self.status_var.set(f"No changes made to {item_type_name}.")
            window.destroy()
        save_btn = tk.Button(button_frame, text="Save Changes", width=12, command=save_changes)
        save_btn.pack(side=tk.RIGHT, padx=5)
        cancel_btn = tk.Button(button_frame, text="Cancel", width=12, command=window.destroy)
        cancel_btn.pack(side=tk.RIGHT)
        item_entry.focus_set(); window.wait_window()


    def manage_entity_tags(self):
        self._manage_items("Entity Tags", self.entity_tags, self._update_entity_tag_combobox)


    def manage_relation_types(self):
        self._manage_items("Relation Types", self.relation_types, self._update_relation_type_combobox)


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
