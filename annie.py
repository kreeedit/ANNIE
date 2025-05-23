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
"""

import os
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import json
from pathlib import Path
import uuid  # For unique IDs
import itertools # For cycling through colors
import re

# --- Constants ---
SESSION_FILE_VERSION = "1.10" # Incremented version for overlap fix

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
        # Main annotation data structure:
        # { "full/path/to/file.txt": {"entities": [entity_dict,...], "relations": [relation_dict,...]}, ... }
        # Entity dict may include 'propagated': True
        self.annotations = {}
        self.session_save_path = None # Track the path of the last saved/loaded session

        # --- Entity Tagging Configuration ---
        self.entity_tags = ["Person", "Organization", "Location", "Date", "Other"]
        self.selected_entity_tag = tk.StringVar(value=self.entity_tags[0] if self.entity_tags else "")
        self.extend_to_word = tk.BooleanVar(value=False) # For entity propagation

        # --- Relation Tagging Configuration ---
        self.relation_types = ["spouse_of", "works_at", "located_in", "born_on", "produces"]
        self.selected_relation_type = tk.StringVar(value=self.relation_types[0] if self.relation_types else "")

        # --- UI State ---
        self.selected_entity_ids_for_relation = [] # Stores actual entity UUIDs selected in entities_tree
        self._entity_id_to_tree_iids = {} # Maps actual entity ID to list of tree row iids using it

        # --- Sort Tracking ---
        self.entities_sort_column = None
        self.entities_sort_reverse = False
        self.relations_sort_column = None
        self.relations_sort_reverse = False

        # --- Colors ---
        self.tag_colors = { # Default colors
            "Person": "#ffcccc", "Organization": "#ccffcc", "Location": "#ccccff",
            "Date": "#ffffcc", "Other": "#ccffff"
        }
        self.color_cycle = itertools.cycle([ # Fallback colors
            "#e6e6fa", "#ffe4e1", "#f0fff0", "#fffacd", "#add8e6",
            "#f5f5dc", "#d3ffd3", "#fafad2", "#ffebcd", "#e0ffff"
        ])
        self._ensure_default_colors() # Ensure default tags have colors assigned

        # --- Build UI ---
        self.create_menu()
        self.create_layout() # This creates self.text_area

        # --- Status Bar ---
        self.status_var = tk.StringVar(value="Ready. Open a directory or load a session.")
        self.status_bar = tk.Label(self.root, textvariable=self.status_var, bd=1, relief=tk.SUNKEN, anchor=tk.W)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)

        # --- Initial UI Setup ---
        self._update_entity_tag_combobox()
        self._update_relation_type_combobox()
        self._configure_text_tags() # Configures entity background AND propagated underline tags
        self._configure_treeview_tags()
        self._update_button_states() # Initial state

        # --- Add protocol for closing window ---
        self.root.protocol("WM_DELETE_WINDOW", self._on_closing)

        # Bind mouse events for annotation/removal - Done in create_layout now


    def _ensure_default_colors(self):
        """Ensure all predefined entity tags have a color assigned."""
        for tag in self.entity_tags:
            self.get_color_for_tag(tag) # This will assign a color if missing


    def create_menu(self):
        """Creates the main application menu bar."""
        menubar = tk.Menu(self.root)

        # File menu
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Open Directory", command=self.load_directory)
        file_menu.add_separator()
        # --- Session Save/Load ---
        file_menu.add_command(label="Load Session...", command=self.load_session)
        file_menu.add_command(label="Save Session", command=self.save_session)
        file_menu.add_command(label="Save Session As...", command=lambda: self.save_session(force_ask=True))
        file_menu.add_separator()
        # --- End ---
        file_menu.add_command(label="Save Annotations Only...", command=self.save_annotations)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self._on_closing)
        menubar.add_cascade(label="File", menu=file_menu)

        # Settings menu
        settings_menu = tk.Menu(menubar, tearoff=0)
        settings_menu.add_command(label="Manage Entity Tags...", command=self.manage_entity_tags)
        settings_menu.add_command(label="Manage Relation Types...", command=self.manage_relation_types)
        settings_menu.add_separator()
        settings_menu.add_command(label="Load Dictionary & Propagate Entities...", command=self.load_and_propagate_from_dictionary)
        menubar.add_cascade(label="Settings", menu=settings_menu)

        self.root.config(menu=menubar)

    # --- UI Layout Creation ---
    def create_layout(self):
        """Creates the main GUI layout with all widgets."""
        # Main frame
        main_frame = tk.Frame(self.root)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        # --- Left panel: File list and navigation ---
        left_frame = tk.Frame(main_frame, width=200)
        left_frame.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 10))
        left_frame.pack_propagate(False) # Prevent frame from shrinking
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

        # --- Right panel: Text area, controls, and annotation lists ---
        right_frame = tk.Frame(main_frame)
        right_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)

        # --- Main Vertical Paned Window for Right Panel ---
        right_main_pane = tk.PanedWindow(right_frame, orient=tk.VERTICAL, sashrelief=tk.RAISED, sashwidth=6)
        right_main_pane.pack(fill=tk.BOTH, expand=True)

        # --- Pane 1: Text Area ---
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
            undo=True, state=tk.DISABLED, # Start disabled
            borderwidth=1, relief="sunken"
            # State will be managed by load_file and annotate_selection
        )
        self.text_area.pack(fill=tk.BOTH, expand=True)
        scrollbar_text_y.config(command=self.text_area.yview)
        scrollbar_text_x.config(command=self.text_area.xview)

        # --- BIND MOUSE EVENTS ---
        self.text_area.bind("<Double-Button-1>", self._on_double_click)
        self.text_area.bind("<ButtonRelease-1>", self._on_highlight_release)
        self.text_area.bind("<Button-1>", self._on_single_click) # For removal
        # Keep existing right-click binding for demerge
        self.text_area.bind("<Button-3>", self._on_text_right_click)
        self.text_area.bind("<Button-2>", self._on_text_right_click)
        # --- END BINDINGS ---

        # --- Pane 2: Controls Panel ---
        controls_panel = tk.Frame(right_main_pane, bd=1, relief=tk.SUNKEN)
        right_main_pane.add(controls_panel, stretch="never")

        # Entity Controls Frame
        entity_controls_frame = tk.LabelFrame(controls_panel, text="Entity Annotation", padx=5, pady=5)
        entity_controls_frame.pack(side=tk.LEFT, padx=(5, 5), pady=5, fill=tk.X, expand=True)

        ecf_top = tk.Frame(entity_controls_frame)
        ecf_top.grid(row=0, column=0, sticky="ew", pady=(0, 5))
        tk.Label(ecf_top, text="Tag:").pack(side=tk.LEFT)
        self.entity_tag_combobox = ttk.Combobox(ecf_top, textvariable=self.selected_entity_tag, values=self.entity_tags, width=12, state="readonly")
        self.entity_tag_combobox.pack(side=tk.LEFT, padx=5)
        # Annotate button still exists but mainly for context if needed; primary way is click/highlight
        self.annotate_btn = tk.Button(ecf_top, text="Annotate Sel", command=self.annotate_selection, state=tk.DISABLED, width=10)
        self.annotate_btn.pack(side=tk.LEFT, padx=5)
        # Remove button works on Treeview selection
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

        # Relation Controls Frame
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


        # --- Pane 3: Annotation Lists (Entities & Relations) ---
        list_outer_frame = tk.Frame(right_main_pane)
        right_main_pane.add(list_outer_frame, stretch="always", minsize=150)
        list_panel = tk.PanedWindow(list_outer_frame, orient=tk.VERTICAL, sashrelief=tk.RAISED, sashwidth=4)
        list_panel.pack(fill=tk.BOTH, expand=True)

        # Entities List Frame
        entities_list_frame = tk.LabelFrame(list_panel, text="Entities", padx=5, pady=5)
        list_panel.add(entities_list_frame, stretch="always", minsize=75)
        entities_tree_frame = tk.Frame(entities_list_frame)
        entities_tree_frame.pack(fill=tk.BOTH, expand=True)
        scrollbar_entities_y = tk.Scrollbar(entities_tree_frame)
        scrollbar_entities_y.pack(side=tk.RIGHT, fill=tk.Y)
        self.entities_tree = ttk.Treeview(
            entities_tree_frame, columns=("ID", "Start", "End", "Text", "Tag"), # ID column holds actual entity ID
            displaycolumns=("Start", "End", "Text", "Tag"), show="headings",
            yscrollcommand=scrollbar_entities_y.set, selectmode='extended' # 'extended' for multi-select
        )
        self.entities_tree.column("ID", width=0, stretch=False) # Hide actual ID column
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
        scrollbar_entities_y.config(command=self.entities_tree.yview)

        # Relations List Frame
        relations_list_frame = tk.LabelFrame(list_panel, text="Relations", padx=5, pady=5)
        list_panel.add(relations_list_frame, stretch="always", minsize=75)
        relations_tree_frame = tk.Frame(relations_list_frame)
        relations_tree_frame.pack(fill=tk.BOTH, expand=True)
        scrollbar_relations_y = tk.Scrollbar(relations_tree_frame)
        scrollbar_relations_y.pack(side=tk.RIGHT, fill=tk.Y)
        self.relations_tree = ttk.Treeview(
            relations_tree_frame, columns=("ID", "Head", "Type", "Tail"), # ID column holds relation ID
            displaycolumns=("Head", "Type", "Tail"), show="headings",
            yscrollcommand=scrollbar_relations_y.set, selectmode='browse' # 'browse' for single select
        )
        self.relations_tree.column("ID", width=0, stretch=False) # Hide relation ID column
        self.relations_tree.heading("Head", text="Head Entity", command=lambda: self._treeview_sort_column(self.relations_tree, "Head", False))
        self.relations_tree.heading("Type", text="Relation Type", command=lambda: self._treeview_sort_column(self.relations_tree, "Type", False))
        self.relations_tree.heading("Tail", text="Tail Entity", command=lambda: self._treeview_sort_column(self.relations_tree, "Tail", False))
        self.relations_tree.column("Head", width=250, anchor=tk.W, stretch=True)
        self.relations_tree.column("Type", width=120, anchor=tk.CENTER, stretch=False)
        self.relations_tree.column("Tail", width=250, anchor=tk.W, stretch=True)
        self.relations_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.relations_tree.bind("<<TreeviewSelect>>", self.on_relation_select)
        self.relations_tree.bind("<Key>", lambda event: self._treeview_key_navigate(self.relations_tree, event)) # Added navigation
        scrollbar_relations_y.config(command=self.relations_tree.yview)

    # --- Treeview Sorting and Navigation ---
    def _treeview_sort_column(self, tree, col, reverse):
        """Sorts a Treeview by the specified column."""
        # Special handling for Start/End columns - sort numerically by line then char
        if col in ["Start", "End"] and tree == self.entities_tree:
            data = []
            for item in tree.get_children(""):
                pos_str = tree.set(item, col)
                try:
                    line, char = map(int, pos_str.split('.'))
                    data.append(((line, char), item))
                except ValueError:
                    data.append(((0, 0), item)) # Fallback for invalid format
        else:
            # Default string-based sorting (case-insensitive)
            data = [(tree.set(item, col).lower(), item) for item in tree.get_children("")]


        # Store current selection before sorting
        selection = tree.selection()

        # Perform the sort
        data.sort(reverse=reverse)

        # Move items in the tree according to sort order
        for index, (val, item) in enumerate(data):
            tree.move(item, "", index)

        # Restore selection (if it still exists after potential data changes)
        valid_selection = [s for s in selection if tree.exists(s)]
        if valid_selection:
            tree.selection_set(valid_selection)
            # Make first selected item visible
            if tree.exists(valid_selection[0]):
                tree.see(valid_selection[0])
        else:
            # Clear internal selection state if selection is gone
            if tree == self.entities_tree:
                self.selected_entity_ids_for_relation = []
            # Trigger update buttons based on lack of selection
            self._update_button_states()


        # Update the header to show sort direction
        # First reset all headers to remove previous indicators
        tree_columns = tree["columns"]
        display_columns = tree["displaycolumns"] if tree["displaycolumns"] != "#all" else tree_columns
        for column in display_columns:
            try:
                current_text = tree.heading(column, 'text')
                # Remove indicator if present
                base_text = current_text.replace(" ▲", "").replace(" ▼", "")
                tree.heading(column, text=base_text)
            except tk.TclError: pass # Ignore errors on hidden columns like ID

        # Update current sort column header
        indicator = "▼" if reverse else "▲"
        try:
            current_text = tree.heading(col, 'text')
            base_text = current_text.replace(" ▲", "").replace(" ▼", "") # Ensure clean base
            tree.heading(col, text=f"{base_text} {indicator}",
                         command=lambda c=col: self._treeview_sort_column(tree, c, not reverse))
        except tk.TclError: pass # Ignore if column doesn't exist or isn't displayed


    def _treeview_key_navigate(self, tree, event):
        """Handles keyboard navigation in a Treeview to jump to items starting with pressed letter."""
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

    # --- Mouse Event Handlers for Text Area ---

    def _on_double_click(self, event):
        """Handles double-click.
        Prevents annotation if the exact word span is already annotated OR
        if the click occurs within any existing annotation span.
        Otherwise, selects the word and attempts annotation via annotate_selection.
        """
        if not self.current_file_path or not self.entity_tags:
            return "break" # Prevent default behavior if no file/tags

        original_state = self.text_area.cget('state')
        needs_re_disable = False
        # Temporarily enable to get indices/word boundaries if needed
        if original_state == tk.DISABLED:
            try:
                # Only enable if we actually need to read indices/perform actions
                self.text_area.config(state=tk.NORMAL)
                needs_re_disable = True
            except tk.TclError:
                print("Warning: Could not enable text area state for double-click.")
                return "break" # Cannot proceed reliably

        try:
            # --- Step 1: Get click position and word span indices ---
            click_index_str = self.text_area.index(f"@{event.x},{event.y}")
            word_start_str = self.text_area.index(f"{click_index_str} wordstart")
            word_end_str = self.text_area.index(f"{click_index_str} wordend")

            # If word start/end are the same, it's likely not a valid word target (e.g., empty line)
            if word_start_str == word_end_str:
                 # print("Debug: Double-click on non-word area or empty selection.") # Optional debug
                 return "break"

            # --- Step 2: Check if this exact word span is already annotated ---
            try:
                potential_start_l, potential_start_c = map(int, word_start_str.split('.'))
                potential_end_l, potential_end_c = map(int, word_end_str.split('.'))
            except ValueError:
                print(f"Warning: Could not parse word boundaries: {word_start_str} / {word_end_str}")
                return "break" # Cannot proceed

            entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
            exact_span_already_exists = False
            for entity in entities:
                start_l, start_c = entity.get('start_line'), entity.get('start_char')
                end_l, end_c = entity.get('end_line'), entity.get('end_char')
                # Ensure coordinates are valid before comparing
                if None not in [start_l, start_c, end_l, end_c]:
                    # Compare numeric line/char values for exact match
                    if (potential_start_l == start_l and potential_start_c == start_c and
                        potential_end_l == end_l and potential_end_c == end_c):
                        exact_span_already_exists = True
                        # Optional: Maybe select the existing annotation in the list?
                        # self._select_entity_in_tree_by_data(entity) # Need to implement this helper
                        break

            if exact_span_already_exists:
                # The exact word/span is already annotated. Stop.
                self.status_var.set("Word span already annotated.") # Provide feedback
                return "break" # Prevent annotation attempt

            # --- Step 3: Check if the click was *on* the text of any existing annotation ---
            # This prevents trying to annotate if you double-click whitespace *within*
            # a larger annotation, even if the exact word span wasn't matched above.
            try:
                 click_line, click_char = map(int, click_index_str.split('.'))
                 click_pos = (click_line, click_char)
                 clicked_on_existing_text = False
                 for entity in reversed(entities): # Check topmost first
                     start_l, start_c = entity.get('start_line'), entity.get('start_char')
                     end_l, end_c = entity.get('end_line'), entity.get('end_char')
                     if None not in [start_l, start_c, end_l, end_c]:
                         span_start = (start_l, start_c)
                         span_end = (end_l, end_c)
                         # Check if click is within [start, end)
                         if span_start <= click_pos < span_end:
                             clicked_on_existing_text = True
                             # Optional: Select the annotation clicked on?
                             # self._select_entity_in_tree_by_data(entity)
                             break
            except ValueError:
                 # Should be unlikely if word boundary check passed, but check anyway
                 print(f"Warning: Could not parse click index: {click_index_str}")
                 return "break"

            if clicked_on_existing_text:
                # Clicked *on* an existing annotation's highlighted text. Stop.
                self.status_var.set("Clicked on existing annotation.") # Provide feedback
                return "break" # Prevent annotation attempt

            # --- Step 4: If checks pass, select the word and trigger annotation ---
            # Ensure state is NORMAL if it wasn't already (needed for tag_add)
            if self.text_area.cget('state') == tk.DISABLED:
                 self.text_area.config(state=tk.NORMAL)
                 needs_re_disable = True # Mark that we definitely need to disable later

            # Clear any previous tk.SEL highlight and select the target word
            self.text_area.tag_remove(tk.SEL, "1.0", tk.END)
            self.text_area.tag_add(tk.SEL, word_start_str, word_end_str)

            # Call annotate_selection - it handles whitespace stripping and final overlap checks itself
            self.annotate_selection()

            # Explicitly clear the selection *after* the annotation attempt
            # to prevent the subsequent ButtonRelease-1 handler (if any) from using it again.
            try:
                self.text_area.tag_remove(tk.SEL, "1.0", tk.END)
            except tk.TclError:
                 pass # Ignore if no selection exists

        except tk.TclError as e:
             # Ignore common benign errors from clicking outside text or index issues
            if "text doesn't contain" not in str(e).lower() and "bad text index" not in str(e).lower():
                 pass
            else:
                 print(f"Warning: TclError during double-click: {e}")
        except Exception as e:
             print(f"Error during double-click processing: {e}")
             import traceback
             traceback.print_exc() # Print full traceback for unexpected errors
        finally:
            # Always restore original state if it was changed and widget exists
            if self.text_area.winfo_exists():
                # If we temporarily enabled it, disable it again
                if needs_re_disable and self.text_area.cget('state') == tk.NORMAL:
                     try:
                         self.text_area.config(state=tk.DISABLED)
                     except tk.TclError:
                         print("Warning: Could not re-disable text area state after double-click.")
                # If it started NORMAL but somehow became DISABLED during the try block
                # without needs_re_disable being True (unlikely), restore it.
                elif not needs_re_disable and self.text_area.cget('state') == tk.DISABLED and original_state == tk.NORMAL:
                     try:
                         self.text_area.config(state=tk.NORMAL)
                     except tk.TclError:
                          print("Warning: Could not restore text area to NORMAL state after double-click.")


        # Ensure this return is also indented correctly within the function
        return "break" # Prevent other bindings (like single-click) from firing

    def _on_highlight_release(self, event):
        """Handles mouse release after highlighting to trigger annotation."""
        if not self.current_file_path or not self.entity_tags:
            return # Nothing to do

        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL) # Need to enable to check tk.SEL
        try:
            # Check if a selection range exists
            if self.text_area.tag_ranges(tk.SEL):
                # Check if the selection start/end are different (ignore single clicks)
                sel_start = self.text_area.index(tk.SEL_FIRST)
                sel_end = self.text_area.index(tk.SEL_LAST)
                if sel_start != sel_end:
                    # If drag selection occurred, call annotate
                    self.annotate_selection()
            # No else needed, if no selection or single click, do nothing here
        except tk.TclError as e:
             # Ignore "text doesn't contain selection" which happens on single clicks without drag
             if "text doesn't contain selection" not in str(e).lower():
                 print(f"Warning: Highlight release error: {e}")
        except Exception as e:
             print(f"Error during highlight release annotation: {e}")
        finally:
             if self.text_area.winfo_exists():
                 self.text_area.config(state=original_state)
        # Don't return "break", allow other release bindings if any

    def _on_single_click(self, event):
        """Handles single-click to potentially remove an annotation."""
        if not self.current_file_path:
            return # Nothing to do if no file

        original_state = self.text_area.cget('state')
        # Reading index might work even if disabled, but enable if needed
        # self.text_area.config(state=tk.NORMAL)
        try:
            click_index_str = self.text_area.index(f"@{event.x},{event.y}")
            click_line, click_char = map(int, click_index_str.split('.'))
            click_pos = (click_line, click_char)

            clicked_entity_dict = None
            entities = self.annotations.get(self.current_file_path, {}).get("entities", [])

            # Iterate reversed to find the topmost entity if overlapping
            for entity in reversed(entities):
                start_l = entity.get('start_line')
                start_c = entity.get('start_char')
                end_l = entity.get('end_line')
                end_c = entity.get('end_char')
                if None in [start_l, start_c, end_l, end_c]: continue

                # Check if click is within the entity span [start, end)
                span_start = (start_l, start_c)
                span_end = (end_l, end_c)

                if span_start <= click_pos < span_end:
                    clicked_entity_dict = entity
                    break # Found the topmost entity under the click

            if clicked_entity_dict:
                # Found an entity, proceed with removal logic
                self._remove_entity_instance(clicked_entity_dict)
                # If an entity was removed, prevent default click behavior (like starting selection)
                return "break"

            # If no entity was clicked, allow default behavior (e.g., set cursor, start selection)

        except tk.TclError:
             pass # Ignore clicking outside text content
        except Exception as e:
             print(f"Error during single-click check: {e}")
        # finally: # Restore state if changed
        #     if self.text_area.winfo_exists() and self.text_area.cget('state') == tk.NORMAL:
        #         self.text_area.config(state=original_state)

    def _remove_entity_instance(self, entity_to_remove):
        """Helper method to remove a specific entity instance clicked in the text area."""
        if not self.current_file_path or self.current_file_path not in self.annotations:
            return

        file_data = self.annotations[self.current_file_path]
        entities_list = file_data.get("entities", [])
        relations_list = file_data.get("relations", [])

        # Find the exact dictionary instance in the list
        entity_index_to_remove = -1
        for i, entity in enumerate(entities_list):
            # Match based on unique properties (ID and position should be sufficient)
            if (entity.get('id') == entity_to_remove.get('id') and
                entity.get('start_line') == entity_to_remove.get('start_line') and
                entity.get('start_char') == entity_to_remove.get('start_char') and
                entity.get('end_line') == entity_to_remove.get('end_line') and
                entity.get('end_char') == entity_to_remove.get('end_char')):
                entity_index_to_remove = i
                break

        if entity_index_to_remove == -1:
            messagebox.showerror("Error", "Could not find the clicked entity instance to remove.", parent=self.root)
            return

        entity_id_being_removed = entity_to_remove.get('id')
        entity_text = entity_to_remove.get('text', '')[:30]

        confirm = messagebox.askyesno("Confirm Removal",
                                      f"Remove annotation for '{entity_text}...'?\n"
                                      f"(Instance ID: {entity_id_being_removed[:8]}...)\n"
                                      f"WARNING: May remove associated relations if this is the last instance.",
                                      parent=self.root)
        if not confirm:
            self.status_var.set("Removal cancelled.")
            return

        # Remove the specific entity instance
        del entities_list[entity_index_to_remove]
        removed_entity_count = 1

        # Check if any other instances of this entity ID remain
        id_still_exists = any(e.get('id') == entity_id_being_removed for e in entities_list)

        removed_relation_count = 0
        if not id_still_exists and relations_list:
            # If it was the last instance, remove relations associated with this ID
            relations_original_count = len(relations_list)
            relations_remaining = [rel for rel in relations_list if
                                   rel.get('head_id') != entity_id_being_removed and
                                   rel.get('tail_id') != entity_id_being_removed]
            removed_relation_count = relations_original_count - len(relations_remaining)
            file_data["relations"] = relations_remaining

        # Update UI
        self.update_entities_list() # Also updates internal selection state
        self.update_relations_list()
        self.apply_annotations_to_text() # Re-apply remaining highlights
        self._update_button_states()

        status_msg = f"Removed annotation for '{entity_text}...'"
        if removed_relation_count > 0:
            status_msg += f" and {removed_relation_count} associated relations."
        self.status_var.set(status_msg)

    # --- END NEW Mouse Event Handlers ---


    # --- Color and Tag Configuration ---
    def get_color_for_tag(self, tag):
        """Gets a color for a tag, generating one if not predefined."""
        if tag not in self.tag_colors:
            try:
                if tag in self.entity_tags:
                    self.tag_colors[tag] = next(self.color_cycle)
                else:
                    return "#cccccc" # Default grey for unknown/removed tags
            except Exception:
                self.tag_colors[tag] = "#cccccc" # Fallback
        return self.tag_colors.get(tag, "#cccccc")

    def _configure_text_tags(self):
        """Configures background colors for entity tags and underline for propagated."""
        for tag in self.entity_tags:
            color = self.get_color_for_tag(tag)
            try:
                self.text_area.tag_configure(tag, background=color, underline=False)
            except tk.TclError as e:
                print(f"Warning: Could not configure text tag '{tag}': {e}")

        try:
            self.text_area.tag_configure("propagated_entity", underline=True)
        except tk.TclError as e:
            print(f"Warning: Could not configure text tag 'propagated_entity': {e}")


    def _configure_treeview_tags(self):
        """Configures tags for styling the Treeview items (e.g., for merged entities)."""
        try:
            self.entities_tree.tag_configure(
                'merged',
                foreground='grey',
                font=('TkDefaultFont', 9, 'italic')
            )
        except tk.TclError as e:
            print(f"Warning: Could not configure Treeview tags: {e}")

    def _update_entity_tag_combobox(self):
        """Updates the values and state of the entity tag combobox."""
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
        """Updates the values and state of the relation type combobox."""
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

    # --- Button State Management ---
    def _update_button_states(self):
        """Enable/disable buttons based on current application state."""
        file_loaded = bool(self.current_file_path)
        has_files = bool(self.files_list)
        num_entities_selected_rows = len(self.entities_tree.selection())
        num_relations_selected = len(self.relations_tree.selection())

        # File Navigation
        self.prev_btn.config(state=tk.NORMAL if has_files and self.current_file_index > 0 else tk.DISABLED)
        self.next_btn.config(state=tk.NORMAL if has_files and self.current_file_index < len(self.files_list) - 1 else tk.DISABLED)

        # Entity Buttons
        # Enable Annotate Sel button if a file is loaded AND entity tags exist.
        can_annotate_entity_button = file_loaded and self.entity_tags
        self.annotate_btn.config(state=tk.NORMAL if can_annotate_entity_button else tk.DISABLED)
        # Remove Sel button depends on Treeview selection
        self.remove_entity_btn.config(state=tk.NORMAL if num_entities_selected_rows > 0 else tk.DISABLED)
        self.merge_entities_btn.config(state=tk.NORMAL if num_entities_selected_rows >= 2 else tk.DISABLED)
        # Enable propagation if file loaded and *any* annotations exist in the current file
        can_propagate_current = file_loaded and self.annotations.get(self.current_file_path, {}).get("entities")
        self.propagate_btn.config(state=tk.NORMAL if can_propagate_current else tk.DISABLED)


        # Relation Buttons
        # Enable Add Relation if exactly two unique entity *IDs* are selected (from the internal list)
        can_add_relation = len(self.selected_entity_ids_for_relation) == 2 and self.relation_types
        self.add_relation_btn.config(state=tk.NORMAL if can_add_relation else tk.DISABLED)

        can_modify_relation = num_relations_selected == 1
        self.flip_relation_btn.config(state=tk.NORMAL if can_modify_relation else tk.DISABLED)
        self.remove_relation_btn.config(state=tk.NORMAL if can_modify_relation else tk.DISABLED)


    # --- File Handling ---
    def load_directory(self):
        """Opens a directory, lists .txt files, and loads the first one."""
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
                messagebox.showerror("Error Loading Directory", f"Could not read directory contents:\n{e}")
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

    def load_file(self, index):
        """Loads the content and annotations for the file at the given index. Makes text area read-only."""
        if not (0 <= index < len(self.files_list)):
            print(f"Warning: Invalid file index {index} requested.")
            return
        if index == self.current_file_index and self.current_file_path:
            return

        self.clear_views() # Clears text, treeviews, selection state

        self.current_file_index = index
        self.current_file_path = self.files_list[index]
        filename = os.path.basename(self.current_file_path)

        # Update listbox selection visually
        self.files_listbox.selection_clear(0, tk.END)
        self.files_listbox.selection_set(index)
        self.files_listbox.activate(index)
        self.files_listbox.see(index)

        # Load file content - Enable temporarily
        self.text_area.config(state=tk.NORMAL)
        self.text_area.delete(1.0, tk.END)
        file_loaded_successfully = False
        try:
            with open(self.current_file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                self.text_area.insert(tk.END, content)
            file_loaded_successfully = True
        except Exception as e:
            messagebox.showerror("Error Reading File", f"Failed to load file '{filename}':\n{str(e)}")
            self.text_area.delete(1.0, tk.END) # Clear partial content if error
            self.text_area.config(state=tk.DISABLED) # Ensure disabled on error
            self.current_file_path = None
            self.status_var.set(f"Error loading {filename}")
            file_loaded_successfully = False
            try: self.entities_tree.delete(*self.entities_tree.get_children())
            except Exception: pass
            try: self.relations_tree.delete(*self.relations_tree.get_children())
            except Exception: pass
            self.selected_entity_ids_for_relation = []

        # If loaded successfully, apply annotations and disable editing
        if file_loaded_successfully:
            file_data = self.annotations.setdefault(self.current_file_path, {"entities": [], "relations": []})
            file_data.setdefault("entities", [])
            file_data.setdefault("relations", [])

            # Populate UI lists and apply highlighting
            self.update_entities_list()
            self.update_relations_list()
            self.apply_annotations_to_text() # Applies tags/underlines (handles state internally)

            self.status_var.set(f"Loaded: {filename} ({index+1}/{len(self.files_list)})")

            # Reset undo stack for the new file
            self.text_area.edit_reset()

            # --- MAKE TEXT AREA READ-ONLY ---
            self.text_area.config(state=tk.DISABLED)
            # ---------------------------------

        # Always update button states after load attempt
        self._update_button_states()

    def clear_views(self):
        """Clears text area content, highlights, and annotation list Treeviews."""
        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL) # Enable to modify
        try:
            self.text_area.delete(1.0, tk.END)
            # Remove all known entity tag highlights AND propagated underline tag
            current_text_tags = list(self.text_area.tag_names())
            tags_to_remove = set(self.entity_tags)
            tags_to_remove.add("propagated_entity")

            for tag_name in current_text_tags:
                if tag_name in tags_to_remove and tag_name != tk.SEL:
                    try: self.text_area.tag_remove(tag_name, "1.0", tk.END)
                    except tk.TclError: pass # Ignore if tag doesn't exist

            # Remove selection highlight specifically
            try: self.text_area.tag_remove(tk.SEL, "1.0", tk.END)
            except tk.TclError: pass
        finally:
            # Restore original state OR set to disabled if no file path is set
            if self.text_area.winfo_exists():
                 self.text_area.config(state=tk.DISABLED if not self.current_file_path else original_state)


        # Clear Treeviews safely
        try: self.entities_tree.delete(*self.entities_tree.get_children())
        except Exception: pass
        try: self.relations_tree.delete(*self.relations_tree.get_children())
        except Exception: pass

        # Reset selection state variable used for relations
        self.selected_entity_ids_for_relation = []
        self._entity_id_to_tree_iids = {} # Clear mapping too


    def _reset_state(self):
        """Resets the core application state (files, annotations, current index)."""
        self.clear_views() # Clear UI elements first
        self.current_file_path = None
        self.files_list = []
        self.files_listbox.delete(0, tk.END)
        self.current_file_index = -1
        self.annotations = {}
        self.session_save_path = None
        self.root.title("ANNIE - Annotation Interface")
        self.status_var.set("Ready. Open a directory or load a session.")
        # Ensure text area is disabled after reset
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

    # --- Annotation Saving (Annotations ONLY) ---
    def save_annotations(self):
        """Saves ONLY annotations (entities/relations) for all files to a JSON file."""
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
                try: # Use Pathlib check if available (Python 3.9+)
                    if Path(file_path).is_relative_to(save_dir): use_rel_path = True
                except AttributeError: # Fallback for older Python
                    if not os.path.isabs(rel_path) and not rel_path.startswith(('..'+os.sep, '..'+'/')): use_rel_path = True

                if use_rel_path: key = rel_path.replace('\\', '/')
                else: key = os.path.basename(file_path) # Fallback if not relative
            except ValueError: key = os.path.basename(file_path) # Handle different drives
            except Exception as e:
                print(f"Warning: Relative path calculation error: {e}. Using basename.")
                key = os.path.basename(file_path)

            # Sort entities and relations for consistent output
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


    # --- Session Save/Load ---
    def save_session(self, force_ask=False):
        """Saves the entire application state to a session file."""
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
            "extend_to_word": self.extend_to_word.get()
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
            self.session_save_path = None # Clear path on error

    def load_session(self):
        """Loads application state from a session file."""
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

        # --- Validation ---
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
            msg = "Some text files referenced could not be found:\n"
            msg += "\n".join([f"- {os.path.basename(mf)}" for mf in missing_files[:5]])
            if len(missing_files) > 5: msg += "\n..."
            msg += "\n\nContinue loading session?"
            if not messagebox.askyesno("Missing Files", msg, parent=self.root):
                self.status_var.set("Load session cancelled due to missing files."); return

        # --- Restore State ---
        self._reset_state()
        try:
            self.files_list = loaded_files_list
            self.current_file_index = session_data["current_file_index"]
            self.annotations = session_data["annotations"]
            self.entity_tags = session_data["entity_tags"]
            self.relation_types = session_data["relation_types"]
            self.tag_colors = session_data["tag_colors"]
            self.extend_to_word.set(session_data.get("extend_to_word", False)) # Load extend option, default False
            self.session_save_path = load_path

            # --- Update UI ---
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
                    self.status_var.set(f"Session loaded. Current file missing.")
                    self.clear_views() # Clear views but keep listbox
                    # Visually select missing file in listbox
                    self.files_listbox.selection_clear(0, tk.END)
                    self.files_listbox.selection_set(self.current_file_index)
                    self.files_listbox.activate(self.current_file_index)
                    self.files_listbox.see(self.current_file_index)
                    self._update_button_states()
                else:
                    # Use a temporary variable to ensure load_file works correctly
                    current_idx_temp = self.current_file_index
                    self.current_file_index = -1 # Force load_file to actually load
                    self.load_file(current_idx_temp)
            else:
                self.status_var.set("Session loaded, but no files to display.")
                self.clear_views(); self._update_button_states()

            # Update window title
            base_dir_name = "Session"
            if self.files_list:
                try: base_dir_name = os.path.basename(os.path.dirname(self.files_list[0]))
                except: pass
            self.root.title(f"ANNIE - {base_dir_name} [{os.path.basename(load_path)}]")

        except Exception as e:
             messagebox.showerror("Load Session Error", f"Error applying session data:\n{e}", parent=self.root)
             self._reset_state(); self._update_button_states()


    # --- Check for Unsaved Changes ---
    def _has_unsaved_changes(self):
        """Checks if there are potential unsaved changes in the current session."""
        # A simple check: if files are loaded, assume potential changes.
        # More sophisticated checks could compare current state to last saved state.
        return bool(self.files_list)

    def _on_closing(self):
        """Handles the window close event."""
        if self._has_unsaved_changes():
            response = messagebox.askyesnocancel("Exit Confirmation", "You have an active session.\nSave session before exiting?", parent=self.root)
            if response is True: # Yes
                self.save_session()
                # Check if save was successful (or not cancelled) before quitting
                # save_session sets self.session_save_path on success
                if self.session_save_path: # Check if a path exists (implies successful or previous save)
                     # Check if the status bar indicates a successful save rather than cancel/error
                     if "saved to" in self.status_var.get().lower():
                         self.root.quit()
                     # else: Save might have failed or been cancelled, don't quit
                # else: Save was likely cancelled or never happened, don't quit
            elif response is False: # No
                self.root.quit()
            # else: Cancel - do nothing
        else:
            self.root.quit()


    # --- Entity Annotation ---
    def _spans_overlap_numeric(self, start1_line, start1_char, end1_line, end1_char,
                               start2_line, start2_char, end2_line, end2_char):
        """Checks if two spans, defined by line/char numbers, overlap.
           Intervals are [start, end) - the end character is NOT included."""
        span1_start = (start1_line, start1_char)
        span1_end = (end1_line, end1_char)
        span2_start = (start2_line, start2_char)
        span2_end = (end2_line, end2_char)

        # Ensure start <= end for comparison consistency (should already be true)
        # if span1_start > span1_end: span1_start, span1_end = span1_end, span1_start # Should not happen with tk indices
        # if span2_start > span2_end: span2_start, span2_end = span2_end, span2_start

        # Check for non-overlap: span1 ends before or exactly when span2 starts OR
        #                       span1 starts after or exactly when span2 ends.
        is_disjoint = (span1_end <= span2_start) or (span1_start >= span2_end)

        # Overlap exists if they are NOT disjoint.
        return not is_disjoint

    def _is_overlapping_in_list(self, start_line, start_char, end_line, end_char, existing_entities_list):
        """Checks if the given span overlaps with any entity dict in the provided list."""
        for ann in existing_entities_list:
            if not all(k in ann for k in ['start_line', 'start_char', 'end_line', 'end_char']): continue
            if self._spans_overlap_numeric(start_line, start_char, end_line, end_char,
                                          ann['start_line'], ann['start_char'], ann['end_line'], ann['end_char']):
                return True # Return True on the first overlap found
        return False # Return False if no overlaps found after checking all


    # --- Entity Annotation (Triggered by Clicks/Button) ---
    # --- MODIFIED VERSION BELOW ---
    # --- WITHIN the TextAnnotator class ---

    def annotate_selection(self):
        """Annotates the selected text (stripping whitespace) as an entity.
        Prevents adding if an annotation for the exact same final span already exists.
        Only warns about overlaps with annotations at different spans."""
        if not self.current_file_path:
            return
        if not self.entity_tags:
            messagebox.showwarning("Warning", "No entity tags defined.", parent=self.root); return

        original_state = self.text_area.cget('state')
        # Ensure state is normal for selection reading and potential modification
        # We must be able to read tk.SEL, which requires NORMAL state.
        needs_re_disable = False
        if original_state == tk.DISABLED:
             try:
                 self.text_area.config(state=tk.NORMAL)
                 needs_re_disable = True # Remember to disable later if we enabled it
             except tk.TclError:
                 print("Warning: Could not enable text area state for annotation.")
                 return # Cannot proceed

        try:
            start_pos = self.text_area.index(tk.SEL_FIRST)
            end_pos = self.text_area.index(tk.SEL_LAST)
            # If start/end are same, no selection range exists (might happen on single click artifact)
            if start_pos == end_pos:
                return # Nothing selected to annotate

            selected_text = self.text_area.get(start_pos, end_pos)

            # --- Adjust selection to remove leading/trailing whitespace ---
            adj_start_pos, adj_end_pos = start_pos, end_pos
            adj_selected_text = selected_text
            leading_whitespace = len(selected_text) - len(selected_text.lstrip())
            trailing_whitespace = len(selected_text) - len(selected_text.rstrip())

            if leading_whitespace > 0:
                adj_start_pos = self.text_area.index(f"{start_pos}+{leading_whitespace}c")
            if trailing_whitespace > 0:
                # Note: Calculation based on original end_pos minus trailing whitespace
                adj_end_pos = self.text_area.index(f"{end_pos}-{trailing_whitespace}c")

            # Re-get text if positions changed, handle edge case of only whitespace selected
            if leading_whitespace > 0 or trailing_whitespace > 0:
                if self.text_area.compare(adj_start_pos, ">=", adj_end_pos):
                     # Adjusted span is invalid or empty (only whitespace)
                     return # Silently return, nothing to annotate
                try:
                     adj_selected_text = self.text_area.get(adj_start_pos, adj_end_pos)
                except tk.TclError: # Handle cases where adjusted indices become invalid
                     return # Cannot annotate
                if not adj_selected_text.strip():
                     # Double check after getting adjusted text
                     return # Nothing to annotate

            # Use adjusted positions and stripped text
            try:
                start_line, start_char = map(int, adj_start_pos.split('.'))
                end_line, end_char = map(int, adj_end_pos.split('.'))
            except ValueError:
                print(f"Error parsing adjusted positions: {adj_start_pos} / {adj_end_pos}")
                return

            final_text = adj_selected_text.strip()
            if not final_text: # Final safeguard
                return

            tag = self.selected_entity_tag.get()
            if not tag:
                 messagebox.showwarning("Warning", "No entity tag selected.", parent=self.root)
                 return

            # --- *** NEW CHECK: Prevent adding if exact adjusted span already exists *** ---
            entities_in_file = self.annotations.get(self.current_file_path, {}).get("entities", [])
            exact_adjusted_span_exists = False
            for existing_ann in entities_in_file:
                ex_sl, ex_sc = existing_ann.get('start_line'), existing_ann.get('start_char')
                ex_el, ex_ec = existing_ann.get('end_line'), existing_ann.get('end_char')
                # Check if all coordinates are valid before comparing
                if None not in [ex_sl, ex_sc, ex_el, ex_ec]:
                    # Compare numeric line/char values for exact match of the *final* span
                    if (start_line == ex_sl and start_char == ex_sc and
                        end_line == ex_el and end_char == ex_ec):
                        exact_adjusted_span_exists = True
                        break # Found an existing annotation covering the exact same final span

            if exact_adjusted_span_exists:
                # Annotation for this exact text span already exists. Do not add another.
                self.status_var.set("Annotation for this span already exists.")
                # Optionally clear the selection highlight if it wasn't cleared elsewhere
                try: self.text_area.tag_remove(tk.SEL, "1.0", tk.END)
                except tk.TclError: pass
                return # Stop before adding the annotation
            # --- *** END OF NEW CHECK *** ---


            # --- Start of Original Overlap Check (Checks overlaps with DIFFERENT spans) ---
            # This remains useful to prevent partial overlaps with other annotations.
            problematic_overlap_entity = None
            proposed_span_start_tuple = (start_line, start_char)
            proposed_span_end_tuple = (end_line, end_char)

            for existing_ann in entities_in_file: # Check against the list again for partial overlaps
                 # Ensure the existing annotation has all necessary position keys
                 if not all(k in existing_ann for k in ['start_line', 'start_char', 'end_line', 'end_char']):
                     continue

                 existing_start_l = existing_ann['start_line']
                 existing_start_c = existing_ann['start_char']
                 existing_end_l = existing_ann['end_line']
                 existing_end_c = existing_ann['end_char']

                 # 1. Check for *any* spatial overlap using the existing helper function
                 if self._spans_overlap_numeric(start_line, start_char, end_line, end_char,
                                                existing_start_l, existing_start_c,
                                                existing_end_l, existing_end_c):

                     # 2. If there is an overlap, check if it's with the *exact same span*
                     existing_span_start_tuple = (existing_start_l, existing_start_c)
                     existing_span_end_tuple = (existing_end_l, existing_end_c)

                     is_exact_same_span = (proposed_span_start_tuple == existing_span_start_tuple and
                                           proposed_span_end_tuple == existing_span_end_tuple)

                     # 3. If the overlap exists AND it's NOT the exact same span, it's problematic.
                     # (This check is now technically redundant because the exact match was handled above,
                     # but it doesn't hurt to leave it as it correctly identifies partial overlaps)
                     if not is_exact_same_span:
                          problematic_overlap_entity = existing_ann
                          break # Found a problematic overlap

            if problematic_overlap_entity:
                 messagebox.showwarning("Overlap Detected",
                                       f"Proposed annotation span:\n"
                                       f"'{final_text}' ({adj_start_pos} -> {adj_end_pos})\n\n"
                                       f"Overlaps with a different existing entity:\n"
                                       f"'{problematic_overlap_entity.get('text', '')}' ({problematic_overlap_entity.get('tag', '')})\n"
                                       f"({problematic_overlap_entity.get('start_line')}.{problematic_overlap_entity.get('start_char')} -> {problematic_overlap_entity.get('end_line')}.{problematic_overlap_entity.get('end_char')})",
                                       parent=self.root)
                 # Optionally clear selection
                 try: self.text_area.tag_remove(tk.SEL, "1.0", tk.END)
                 except tk.TclError: pass
                 return # Prevent annotation because it overlaps with something *else*
            # --- End of Original Overlap Check ---


            # --- If no exact match and no problematic overlap, proceed to add annotation ---
            file_data = self.annotations.setdefault(self.current_file_path, {"entities": [], "relations": []})
            entities_list = file_data.setdefault("entities", [])
            entity_id = uuid.uuid4().hex
            # Store the annotation using the adjusted start/end and the stripped text
            annotation = {'id': entity_id, 'start_line': start_line, 'start_char': start_char,
                          'end_line': end_line, 'end_char': end_char, 'text': final_text, 'tag': tag}
            entities_list.append(annotation)

            # Optionally clear text selection after annotation (might already be cleared by _on_double_click)
            try:
                self.text_area.tag_remove(tk.SEL, "1.0", tk.END)
            except tk.TclError:
                 pass # Ignore if no selection exists

            self.apply_annotations_to_text() # Re-applies highlights including the new one
            self.update_entities_list() # Updates the treeview

            # --- Select new entity in list ---
            self.root.update_idletasks() # Allow UI to update before searching tree
            try:
                new_tree_row_iid = None
                if entity_id in self._entity_id_to_tree_iids:
                    # Find the specific tree row iid corresponding to the added entity instance
                    for tree_iid in self._entity_id_to_tree_iids[entity_id]:
                         if self.entities_tree.exists(tree_iid): # Check if iid still valid
                             item_values = self.entities_tree.item(tree_iid, 'values')
                             # Check ID and start position match using the string representations
                             if item_values and len(item_values) > 1 and item_values[0] == entity_id and item_values[1] == adj_start_pos:
                                 new_tree_row_iid = tree_iid
                                 break # Found the correct iid

                if new_tree_row_iid and self.entities_tree.exists(new_tree_row_iid):
                    self.entities_tree.selection_set(new_tree_row_iid)
                    self.entities_tree.focus(new_tree_row_iid)
                    self.entities_tree.see(new_tree_row_iid)
                    self.on_entity_select(None) # Trigger highlight update based on selection
                else:
                     print(f"Warning: Could not find/select treeview row for new entity {entity_id} at {adj_start_pos}")
            except Exception as e:
                 print(f"Error selecting new entity in list: {e}")
            # --- End Select new entity ---

            self.status_var.set(f"Annotated: '{final_text[:30].replace(os.linesep, ' ')}...' as {tag}")
            self._update_button_states()

        except tk.TclError as e:
            if "text doesn't contain selection" in str(e).lower():
                 # This can happen if the selection is lost between event triggers
                 pass # Don't show message box, just do nothing
            elif "bad text index" in str(e).lower():
                 print(f"Warning: Bad text index during annotation: {e}")
            else:
                 messagebox.showerror("Annotation Error", f"Tkinter error:\n{e}", parent=self.root)
        except Exception as e:
            messagebox.showerror("Annotation Error", f"Unexpected error during annotation:\n{e}", parent=self.root)
            import traceback
            traceback.print_exc() # Print stack trace for debugging
        finally:
            # Restore original state if it was changed and widget exists
            if self.text_area.winfo_exists():
                # Only disable if we were the ones who enabled it
                if needs_re_disable and self.text_area.cget('state') == tk.NORMAL:
                    try:
                        self.text_area.config(state=tk.DISABLED)
                    except tk.TclError: pass # Ignore error if cannot disable
            # -------------------------------------

    # --- Entity Removal / Merging / Demerging ---
    def remove_entity_annotation(self):
        """Removes selected entities (rows in treeview) and their associated relations."""
        selected_tree_iids = self.entities_tree.selection() # These are tree row iids
        if not selected_tree_iids:
            messagebox.showinfo("Info", "Select one or more entities from the list to remove.", parent=self.root)
            return
        if not self.current_file_path or self.current_file_path not in self.annotations:
            messagebox.showerror("Error", "Cannot remove entity: No file/annotations.", parent=self.root)
            return

        entities_to_remove_data = [] # Store the actual entity dicts to remove
        entity_ids_to_remove = set() # Store unique IDs of entities being removed
        entities_in_file = self.annotations.get(self.current_file_path, {}).get("entities", [])

        for tree_iid in selected_tree_iids:
             if not self.entities_tree.exists(tree_iid): continue
             try:
                 values = self.entities_tree.item(tree_iid, 'values')
                 if not values or len(values) < 3: continue
                 entity_id, start_pos_str, end_pos_str = values[0], values[1], values[2]

                 for entity_dict in entities_in_file:
                     if (entity_dict.get('id') == entity_id and
                         f"{entity_dict.get('start_line')}.{entity_dict.get('start_char')}" == start_pos_str and
                         f"{entity_dict.get('end_line')}.{entity_dict.get('end_char')}" == end_pos_str):
                         entities_to_remove_data.append(entity_dict)
                         entity_ids_to_remove.add(entity_id)
                         break
             except Exception as e:
                 print(f"Warning: Error getting data for selected tree item {tree_iid}: {e}")

        if not entities_to_remove_data:
             messagebox.showerror("Error", "Could not retrieve data for selected entities.", parent=self.root)
             return

        confirm = messagebox.askyesno("Confirm Removal",
            f"Remove {len(entities_to_remove_data)} selected entity instance(s)?\n"
            f"(Actual unique entity IDs affected: {len(entity_ids_to_remove)})\n"
            f"WARNING: Also removes relations associated with these entity IDs.", parent=self.root)
        if not confirm: return

        original_count = len(entities_in_file)
        # Create a set of keys for efficient removal check
        entities_to_remove_keys = set(
            (e.get('id'), e.get('start_line'), e.get('start_char'), e.get('end_line'), e.get('end_char'))
            for e in entities_to_remove_data
        )
        self.annotations[self.current_file_path]["entities"] = [
            e for e in entities_in_file
            if (e.get('id'), e.get('start_line'), e.get('start_char'), e.get('end_line'), e.get('end_char')) not in entities_to_remove_keys
        ]
        removed_entity_count = original_count - len(self.annotations[self.current_file_path]["entities"])

        relations = self.annotations[self.current_file_path].get("relations", [])
        removed_relation_count = 0
        if relations and entity_ids_to_remove:
            relations_original_count = len(relations)
            relations_remaining = [rel for rel in relations if
                                   rel.get('head_id') not in entity_ids_to_remove and
                                   rel.get('tail_id') not in entity_ids_to_remove]
            removed_relation_count = relations_original_count - len(relations_remaining)
            self.annotations[self.current_file_path]["relations"] = relations_remaining

        self.update_entities_list()
        self.update_relations_list()
        self.apply_annotations_to_text() # Re-apply remaining highlights

        self.status_var.set(f"Removed {removed_entity_count} entity instances, {removed_relation_count} relations.")
        self._update_button_states()

    def merge_selected_entities(self):
        """Merges selected entity instances (rows) in the list to share the same actual ID."""
        selected_tree_iids = self.entities_tree.selection()
        if len(selected_tree_iids) < 2:
            messagebox.showinfo("Info", "Select 2+ entity instances to merge.", parent=self.root); return
        if not self.current_file_path or self.current_file_path not in self.annotations:
            messagebox.showerror("Error", "Cannot merge: No file/annotations.", parent=self.root); return

        selected_entities_data = [] # Store the actual entity dicts selected
        entities_in_file = self.annotations.get(self.current_file_path, {}).get("entities", [])
        processed_positions = set() # Avoid processing duplicates if multiple tree rows point to same instance

        for tree_iid in selected_tree_iids:
             if not self.entities_tree.exists(tree_iid): continue
             try:
                 values = self.entities_tree.item(tree_iid, 'values')
                 if not values or len(values) < 3: continue
                 entity_id, start_pos_str, end_pos_str = values[0], values[1], values[2]
                 pos_key = (start_pos_str, end_pos_str)
                 if pos_key in processed_positions: continue

                 for entity_dict in entities_in_file:
                     if (entity_dict.get('id') == entity_id and
                         f"{entity_dict.get('start_line')}.{entity_dict.get('start_char')}" == start_pos_str and
                         f"{entity_dict.get('end_line')}.{entity_dict.get('end_char')}" == end_pos_str):
                         if all(k in entity_dict for k in ['id', 'start_line', 'start_char', 'end_line', 'end_char', 'text']):
                             selected_entities_data.append(entity_dict)
                             processed_positions.add(pos_key)
                         else: print(f"Warning: Skipping entity at {start_pos_str} in merge - missing data.")
                         break
             except Exception as e: print(f"Warning: Error getting data for merge: {e}")

        if len(selected_entities_data) < 2:
             messagebox.showerror("Error", "Need at least two valid instances to merge.", parent=self.root); return

        # Use the first selected entity as the canonical one
        selected_entities_data.sort(key=lambda e: (e.get('start_line', 0), e.get('start_char', 0)))
        canonical_entity_dict = selected_entities_data[0]
        canonical_id = canonical_entity_dict.get('id')
        if not canonical_id: messagebox.showerror("Error", "Failed to get canonical ID.", parent=self.root); return

        ids_to_change = {e.get('id') for e in selected_entities_data if e.get('id') != canonical_id}
        dicts_to_change = [e for e in selected_entities_data if e.get('id') != canonical_id]
        if not dicts_to_change:
             messagebox.showinfo("Info", "Selected instances already share the same ID.", parent=self.root); return

        confirm = messagebox.askyesno("Confirm Merge",
             f"Merge {len(selected_entities_data)} instances to ID of '{canonical_entity_dict.get('text', '')[:20]}...'?\n"
             f"Relations involving changed IDs will be updated. Duplicate relations removed.", parent=self.root)
        if not confirm: self.status_var.set("Merge cancelled."); return

        modified_entity_count = 0; modified_relation_count = 0
        # 1. Update Entity IDs in the main annotations list
        for i, main_list_dict in enumerate(entities_in_file):
             for entity_to_change in dicts_to_change:
                 if (main_list_dict.get('start_line') == entity_to_change.get('start_line') and
                     main_list_dict.get('start_char') == entity_to_change.get('start_char') and
                     main_list_dict.get('end_line') == entity_to_change.get('end_line') and
                     main_list_dict.get('end_char') == entity_to_change.get('end_char') and
                     main_list_dict.get('id') == entity_to_change.get('id')):
                      if entities_in_file[i]['id'] != canonical_id:
                          entities_in_file[i]['id'] = canonical_id
                          modified_entity_count += 1
                      break # Found the matching dict, move to next in main list

        # 2. Update Relation IDs
        relations = self.annotations[self.current_file_path].get("relations", [])
        if relations and ids_to_change:
             for i, rel in enumerate(relations):
                 rel_mod = False
                 if rel.get('head_id') in ids_to_change: relations[i]['head_id'] = canonical_id; rel_mod = True
                 if rel.get('tail_id') in ids_to_change: relations[i]['tail_id'] = canonical_id; rel_mod = True
                 if rel_mod: modified_relation_count += 1

        # 3. Remove duplicate relations that might have been created by the merge
        removed_duplicates = 0
        if relations and modified_relation_count > 0: # Only check if relations were possibly changed
            unique_relations = []; seen_signatures = set()
            for rel in relations:
                sig = (rel.get('head_id'), rel.get('tail_id'), rel.get('type'))
                if sig not in seen_signatures:
                    seen_signatures.add(sig); unique_relations.append(rel)
                else: removed_duplicates += 1
            if removed_duplicates > 0:
                self.annotations[self.current_file_path]["relations"] = unique_relations

        # --- Update UI ---
        self.update_entities_list(); self.update_relations_list(); self.apply_annotations_to_text()
        # Re-select merged items in the Treeview
        self.root.update_idletasks()
        tree_iids_to_reselect = []
        try:
            if canonical_id in self._entity_id_to_tree_iids:
                tree_iids_to_reselect = self._entity_id_to_tree_iids[canonical_id]
            if tree_iids_to_reselect:
                 valid_reselect = [tid for tid in tree_iids_to_reselect if self.entities_tree.exists(tid)]
                 if valid_reselect:
                     self.entities_tree.selection_set(valid_reselect)
                     self.entities_tree.focus(valid_reselect[0])
                     self.entities_tree.see(valid_reselect[0])
                     self.on_entity_select(None) # Update internal selection state
                 else: self.selected_entity_ids_for_relation = []; self._update_button_states() # Clear if items vanished
            else: self.selected_entity_ids_for_relation = []; self._update_button_states() # Clear if ID has no items
        except Exception as e:
             print(f"Warning: Error re-selecting merged entities: {e}")
             self.selected_entity_ids_for_relation = []; self._update_button_states() # Clear on error

        status_msg = f"Merged {modified_entity_count} instances. Updated {modified_relation_count} relation endpoints."
        if removed_duplicates > 0: status_msg += f" Removed {removed_duplicates} duplicate relations."
        self.status_var.set(status_msg)


    def _on_text_right_click(self, event):
        """Handles right-clicks on the text area to show context menu (for Demerge)."""
        if not self.current_file_path: return

        try:
            click_index_str = self.text_area.index(f"@{event.x},{event.y}")
            click_line, click_char = map(int, click_index_str.split('.'))
        except tk.TclError: return # Clicked outside text content

        clicked_entity_dict = None
        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        for entity in reversed(entities): # Find topmost entity under cursor
            start_l, start_c = entity.get('start_line'), entity.get('start_char')
            end_l, end_c = entity.get('end_line'), entity.get('end_char')
            if start_l is None or start_c is None or end_l is None or end_c is None: continue

            span_start = (start_l, start_c); span_end = (end_l, end_c)
            click_pos = (click_line, click_char)
            # Check if click position is within the span [start, end)
            if span_start <= click_pos < span_end:
                 clicked_entity_dict = entity; break

        if not clicked_entity_dict: return # Didn't click on any known entity

        entity_id = clicked_entity_dict.get('id')
        is_merged = False
        if entity_id:
            count = sum(1 for e in entities if e.get('id') == entity_id)
            if count > 1: is_merged = True

        context_menu = tk.Menu(self.root, tearoff=0)
        demerge_state = tk.NORMAL if is_merged else tk.DISABLED
        context_menu.add_command(label="Demerge This Instance", state=demerge_state,
                                 command=lambda e=clicked_entity_dict: self.demerge_entity(e))
        context_menu.add_separator()
        status = "Merged" if is_merged else "Not Merged"
        context_menu.add_command(label=f"ID: {entity_id[:8]}... ({status})", state=tk.DISABLED)
        context_menu.add_command(label=f"Tag: {clicked_entity_dict.get('tag', 'N/A')}", state=tk.DISABLED)
        propagated_status = "Propagated" if clicked_entity_dict.get('propagated', False) else "Manual"
        context_menu.add_command(label=f"Origin: {propagated_status}", state=tk.DISABLED)


        try: context_menu.tk_popup(event.x_root, event.y_root)
        finally: context_menu.grab_release()

    def demerge_entity(self, entity_dict_to_demerge):
        """Assigns a new unique ID to a specific entity instance."""
        if not self.current_file_path: return
        file_data = self.annotations.get(self.current_file_path)
        if not file_data or "entities" not in file_data: return
        entities_list = file_data["entities"]

        found_index = -1
        # Find the exact instance in the list based on ID and position
        for i, entity in enumerate(entities_list):
            if (entity.get('id') == entity_dict_to_demerge.get('id') and
                entity.get('start_line') == entity_dict_to_demerge.get('start_line') and
                entity.get('start_char') == entity_dict_to_demerge.get('start_char') and
                entity.get('end_line') == entity_dict_to_demerge.get('end_line') and
                entity.get('end_char') == entity_dict_to_demerge.get('end_char')):
                found_index = i; break

        if found_index == -1:
             messagebox.showerror("Error", "Could not find entity instance to demerge.", parent=self.root); return

        original_id = entities_list[found_index].get('id'); new_id = uuid.uuid4().hex
        entities_list[found_index]['id'] = new_id

        self.update_entities_list(); self.apply_annotations_to_text(); self.update_relations_list() # Update relations in case selection changes
        demerged_text = entities_list[found_index].get('text', '')[:30]
        self.status_var.set(f"Demerged instance '{demerged_text}...'. New ID assigned.")
        self._update_button_states()

        # Try to select the newly demerged entity in the list
        try:
            self.root.update_idletasks()
            new_tree_row_iid = None
            # Search the treeview for the item with the new ID AND correct original position
            for tree_iid in self.entities_tree.get_children(""):
                row_values = self.entities_tree.item(tree_iid, 'values')
                if row_values and row_values[0] == new_id:
                     # Also check position to ensure we select the correct instance just demerged
                     if (f"{entity_dict_to_demerge['start_line']}.{entity_dict_to_demerge['start_char']}" == row_values[1] and
                         f"{entity_dict_to_demerge['end_line']}.{entity_dict_to_demerge['end_char']}" == row_values[2]):
                         new_tree_row_iid = tree_iid; break
            if new_tree_row_iid and self.entities_tree.exists(new_tree_row_iid):
                self.entities_tree.selection_set(new_tree_row_iid)
                self.entities_tree.focus(new_tree_row_iid)
                self.entities_tree.see(new_tree_row_iid)
                self.on_entity_select(None) # Update internal state
            else: print("Warning: Could not select demerged entity in the list.")
        except Exception as e: print(f"Warning: Could not select demerged entity in the list: {e}")


    # --- Entity Highlighting and List Updates ---
    def apply_annotations_to_text(self):
        """Applies highlighting (bg color and underline) for entities."""
        if not self.current_file_path: return
        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL)
        try:
            # Clear existing annotation highlights first
            current_text_tags = list(self.text_area.tag_names())
            tags_to_remove = set(self.entity_tags)
            tags_to_remove.add("propagated_entity")
            for tag_name in current_text_tags:
                if tag_name in tags_to_remove and tag_name != tk.SEL: # Don't remove selection tag
                    try: self.text_area.tag_remove(tag_name, "1.0", tk.END)
                    except tk.TclError: pass # Ignore errors if tag doesn't exist

            entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
            # Sort by start position to handle overlapping tags correctly (later tags applied on top)
            # For display purposes, sorting might not be strictly needed if tags don't overlap badly,
            # but good practice.
            sorted_entities = sorted(entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0)))

            for ann in sorted_entities:
                try:
                    start_pos = f"{ann['start_line']}.{ann['start_char']}"
                    end_pos = f"{ann['end_line']}.{ann['end_char']}"
                    tag = ann.get('tag'); is_propagated = ann.get('propagated', False)

                    if tag and tag in self.entity_tags:
                        # Ensure tag is configured before applying
                        if tag not in self.text_area.tag_names(): self._configure_text_tags() # Reconfigure if tag was added
                        # Apply background color tag
                        if tag in self.text_area.tag_names(): # Check again after configure attempt
                            self.text_area.tag_add(tag, start_pos, end_pos)
                            # Apply underline tag if propagated
                            if is_propagated:
                                try:
                                    # Ensure propagated tag is configured
                                    if "propagated_entity" not in self.text_area.tag_names():
                                        self.text_area.tag_configure("propagated_entity", underline=True)
                                    self.text_area.tag_add("propagated_entity", start_pos, end_pos)
                                except tk.TclError as e: print(f"Warn: Underline fail for '{tag}': {e}")
                        else: print(f"Warn: Tag '{tag}' unconfigurable in text area.")
                    elif tag: print(f"Warn: Unknown entity tag '{tag}' encountered during highlight.")
                except KeyError as e: print(f"Warn: Highlight fail, missing key {e}: Entity ID {ann.get('id','N/A')}")
                except tk.TclError as e: print(f"Warn: TclError applying highlight: {e}: Entity ID {ann.get('id','N/A')}")
                except Exception as e: print(f"Warn: General highlight fail: {e}: Entity ID {ann.get('id','N/A')}")
        finally:
             # Ensure state is restored even if errors occur
             if self.text_area.winfo_exists():
                 self.text_area.config(state=original_state)


    def update_entities_list(self):
        """Updates the Entities Treeview with entities for the current file."""
        # Preserve selection based on entity data (ID, start, end)
        selected_data_keys = set()
        selected_tree_iids = self.entities_tree.selection()
        for tree_iid in selected_tree_iids:
            if not self.entities_tree.exists(tree_iid): continue
            try:
                vals = self.entities_tree.item(tree_iid, 'values')
                if vals and len(vals) >= 3:
                     selected_data_keys.add( (vals[0], vals[1], vals[2]) ) # (id, start_str, end_str)
            except Exception: pass

        try: self.entities_tree.delete(*self.entities_tree.get_children())
        except Exception: pass
        self._entity_id_to_tree_iids = {} # Reset mapping

        if not self.current_file_path: self._update_button_states(); return
        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        if not entities: self.selected_entity_ids_for_relation = []; self._update_button_states(); return

        # Sort entities for display in the list (e.g., by position)
        sorted_entities = sorted(entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0), a.get('id', '')))

        # Count occurrences of each entity ID to identify merged ones
        entity_id_counts = {}
        for ann in sorted_entities:
             eid = ann.get('id');
             if eid: entity_id_counts[eid] = entity_id_counts.get(eid, 0) + 1

        tree_iids_to_restore = []
        for ann_index, ann in enumerate(sorted_entities):
            entity_id = ann.get('id');
            if not entity_id: continue # Skip if somehow an entity lacks an ID
            try:
                sl, sc = ann['start_line'], ann['start_char']; el, ec = ann['end_line'], ann['end_char']
                start_pos, end_pos = f"{sl}.{sc}", f"{el}.{ec}"
                full_text = ann.get('text', '')
                # Clean display text: replace newlines, limit length
                disp_text = full_text.replace(os.linesep,' ').replace('\n', ' ').replace('\r', ' ')[:60] + ("..." if len(full_text)>60 else "")
                tag = ann.get('tag', 'N/A')
                # Apply 'merged' tag if this ID appears more than once
                tree_tags = ('merged',) if entity_id_counts.get(entity_id, 0) > 1 else ()
                # Use a combination including index to ensure iid is unique even if ID/pos match (though shouldn't happen)
                tree_row_iid = f"entity_{entity_id}_{start_pos}_{ann_index}"
                values = (entity_id, start_pos, end_pos, disp_text, tag)

                self.entities_tree.insert("", tk.END, iid=tree_row_iid, values=values, tags=tree_tags)
                # Update mapping from actual entity ID to Treeview row iid(s)
                if entity_id not in self._entity_id_to_tree_iids: self._entity_id_to_tree_iids[entity_id] = []
                self._entity_id_to_tree_iids[entity_id].append(tree_row_iid)

                # Check if this entity instance was previously selected
                if (entity_id, start_pos, end_pos) in selected_data_keys:
                    tree_iids_to_restore.append(tree_row_iid)
            except KeyError as e: print(f"Error adding entity to list: Missing key {e}")
            except Exception as e: print(f"Error adding entity to list: {e}")

        # Restore selection
        if tree_iids_to_restore:
            try:
                valid_restore = [tid for tid in tree_iids_to_restore if self.entities_tree.exists(tid)]
                if valid_restore:
                    self.entities_tree.selection_set(valid_restore)
                    self.entities_tree.focus(valid_restore[0]) # Focus first selected
                    self.entities_tree.see(valid_restore[0]) # Scroll to first selected
                    self.on_entity_select(None) # Update internal state based on new selection
                else: self.selected_entity_ids_for_relation = [] # Clear if items vanished
            except Exception as e:
                 print(f"Warning: Could not restore selection: {e}")
                 self.selected_entity_ids_for_relation = [] # Clear on error
        else: self.selected_entity_ids_for_relation = [] # Clear if nothing was selected before

        self._update_button_states() # Update buttons based on current selection state


    def on_entity_select(self, event):
        """Handles selection changes in the Entities Treeview."""
        selected_tree_iids = self.entities_tree.selection()
        # Update the internal list of unique *actual entity IDs* selected
        self.selected_entity_ids_for_relation = []
        entity_ids_in_selection = set() # Track unique IDs encountered in selection
        for tree_iid in selected_tree_iids:
             if not self.entities_tree.exists(tree_iid): continue
             try:
                 values = self.entities_tree.item(tree_iid, 'values')
                 if values and len(values) > 0:
                     actual_entity_id = values[0]
                     if actual_entity_id and actual_entity_id not in entity_ids_in_selection:
                         self.selected_entity_ids_for_relation.append(actual_entity_id)
                         entity_ids_in_selection.add(actual_entity_id)
             except Exception as e: print(f"Warning: Could not get entity ID from selection: {e}")

        # Highlight selected entities in the text area
        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL)
        try:
             self.text_area.tag_remove(tk.SEL, "1.0", tk.END) # Clear previous selection highlight
             first_entity_pos = None # To scroll to the first selected entity
             for tree_iid in selected_tree_iids:
                 if not self.entities_tree.exists(tree_iid): continue
                 try:
                     values = self.entities_tree.item(tree_iid, 'values')
                     if values and len(values) >= 3:
                         start_pos_str, end_pos_str = values[1], values[2] # Get start/end pos strings
                         try:
                             self.text_area.tag_add(tk.SEL, start_pos_str, end_pos_str)
                             if first_entity_pos is None: first_entity_pos = start_pos_str
                         except tk.TclError as te: print(f"Warning: Error highlighting entity from list: {te}")
                 except Exception as e: print(f"Warning: Error processing entity selection highlight: {e}")

             # Scroll to the first selected entity instance
             if first_entity_pos:
                 try: self.text_area.see(first_entity_pos)
                 except tk.TclError as e: print(f"Warning: Error scrolling to selected entity: {e}")
        finally:
             if self.text_area.winfo_exists():
                 self.text_area.config(state=original_state)

        self._update_button_states() # Update button states based on selection


    # --- Relation Annotation ---
    def add_relation(self):
        """Adds a relation between the two selected unique entity IDs (Head -> Tail)."""
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

        # Check for duplicate relation
        if any(r.get('head_id') == head_id and r.get('tail_id') == tail_id and r.get('type') == relation_type for r in relations_list):
            messagebox.showwarning("Duplicate Relation", "This exact relation (same Head ID, Tail ID, and Type) already exists.", parent=self.root)
            return

        relation_id = uuid.uuid4().hex
        new_relation = {"id": relation_id, "type": relation_type, "head_id": head_id, "tail_id": tail_id}
        relations_list.append(new_relation)
        self.update_relations_list() # Update the relations Treeview

        # Select the newly added relation in the list
        self.root.update_idletasks()
        try:
            if self.relations_tree.exists(relation_id): # Relation ID is used as iid here
                self.relations_tree.selection_set(relation_id)
                self.relations_tree.focus(relation_id)
                self.relations_tree.see(relation_id)
                self.on_relation_select(None) # Update button states
            else: print(f"Warning: Could not find new relation {relation_id} in tree.")
        except Exception as e: print(f"Error selecting new relation: {e}")

        self.status_var.set(f"Added Relation: {relation_type} ({head_id[:4]}... -> {tail_id[:4]}...)")

    def flip_selected_relation(self):
        """Flips the Head and Tail entity IDs for the selected relation."""
        selected_iids = self.relations_tree.selection()
        if len(selected_iids) != 1: return # Should only be one selected

        relation_id_to_flip = selected_iids[0] # Relation ID is the Treeview iid
        relations = self.annotations.get(self.current_file_path, {}).get("relations")
        if not relations: return

        found = False
        flipped_relation_index = -1
        for i, rel in enumerate(relations):
            if rel.get('id') == relation_id_to_flip:
                current_head, current_tail = rel.get('head_id'), rel.get('tail_id')
                current_type = rel.get('type')
                if current_head and current_tail and current_type:
                    # Check if flipping would create a duplicate
                    if any(r.get('head_id') == current_tail and r.get('tail_id') == current_head and r.get('type') == current_type
                           for r_idx, r in enumerate(relations) if i != r_idx): # Exclude self check
                        messagebox.showwarning("Duplicate Relation", "Flipping this relation would create a duplicate of an existing relation.", parent=self.root)
                        return

                    # Perform the flip
                    relations[i]['head_id'], relations[i]['tail_id'] = current_tail, current_head
                    found = True
                    flipped_relation_index = i
                    break
                else:
                    messagebox.showerror("Data Error", "Selected relation missing Head/Tail ID or Type.", parent=self.root)
                    return

        if found:
            self.update_relations_list() # Refresh the list display
            # Re-select the flipped relation
            self.root.update_idletasks()
            try:
                if self.relations_tree.exists(relation_id_to_flip):
                    self.relations_tree.selection_set(relation_id_to_flip)
                    self.relations_tree.focus(relation_id_to_flip)
                    self.relations_tree.see(relation_id_to_flip)
                    self.on_relation_select(None)
            except Exception as e: print(f"Warning: Error re-selecting flipped relation: {e}")
            self.status_var.set("Relation Head/Tail flipped.")


    def remove_relation_annotation(self):
        """Removes the selected relation from the Relations list."""
        selected_iids = self.relations_tree.selection()
        if len(selected_iids) != 1: return

        relation_id_to_remove = selected_iids[0] # Relation ID is the Treeview iid
        relations = self.annotations.get(self.current_file_path, {}).get("relations")
        if not relations: return

        original_length = len(relations)
        self.annotations[self.current_file_path]["relations"] = [
            rel for rel in relations if rel.get('id') != relation_id_to_remove
        ]

        if len(self.annotations[self.current_file_path]["relations"]) < original_length:
            self.update_relations_list()
            self.status_var.set("Relation removed.")
            self._update_button_states() # Selection will be lost, update buttons
        else:
            messagebox.showwarning("Not Found", "Could not find the selected relation to remove.", parent=self.root)


    def update_relations_list(self):
        """Updates the Relations Treeview with relations for the current file."""
        # Preserve selection based on relation ID
        selected_rel_iids = self.relations_tree.selection()

        try: self.relations_tree.delete(*self.relations_tree.get_children())
        except Exception: pass

        if not self.current_file_path: self._update_button_states(); return

        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        relations = self.annotations.get(self.current_file_path, {}).get("relations", [])

        if not relations: self._update_button_states(); return # No relations to display

        # Create a map from entity ID to its first encountered text for display
        entity_display_map = {}
        processed_ids_for_map = set() # Ensure we only map each ID once (using first occurrence)
        # Sort entities by position to get the 'first' one consistently if merged
        sorted_entities_for_map = sorted(entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0)))
        for entity in sorted_entities_for_map:
             eid = entity.get('id')
             if eid and eid not in processed_ids_for_map:
                 etext = entity.get('text', 'N/A')
                 # Clean display text
                 disp_text = etext.replace(os.linesep,' ').replace('\n', ' ').replace('\r', ' ')[:30] + ("..." if len(etext)>30 else "")
                 entity_display_map[eid] = disp_text
                 processed_ids_for_map.add(eid)

        # Sort relations for consistent display order
        sorted_relations = sorted(relations, key=lambda r: (r.get('type', ''), r.get('head_id',''), r.get('tail_id','')))
        for rel in sorted_relations:
            rel_id, head_id, tail_id, rel_type = rel.get('id'), rel.get('head_id'), rel.get('tail_id'), rel.get('type')
            if not (rel_id and head_id and tail_id and rel_type): continue # Skip incomplete relations

            head_text = entity_display_map.get(head_id, f"<ID: {head_id[:6]}...>") # Fallback display
            tail_text = entity_display_map.get(tail_id, f"<ID: {tail_id[:6]}...>") # Fallback display
            values = (rel_id, head_text, rel_type, tail_text) # Use actual relation ID for hidden column

            try:
                # Use relation ID as the iid for the Treeview row
                self.relations_tree.insert("", tk.END, iid=rel_id, values=values)
            except Exception as e: print(f"Error inserting relation {rel_id} into tree: {e}")

        # Restore selection if possible
        valid_selection = [rid for rid in selected_rel_iids if self.relations_tree.exists(rid)]
        if valid_selection:
            try:
                self.relations_tree.selection_set(valid_selection)
                self.relations_tree.focus(valid_selection[0]) # Focus first selected
                self.relations_tree.see(valid_selection[0]) # Scroll to first selected
            except Exception as e: print(f"Warning: Could not restore relation selection: {e}")

        self._update_button_states() # Update buttons based on selection


    def on_relation_select(self, event):
        """Handles selection changes in the Relations Treeview."""
        # Mainly used to update button states
        self._update_button_states()


    # --- Propagation ---
    def propagate_annotations(self):
        """Propagate ENTITY annotations based on text/tag pairs from the *current* file to ALL files."""
        if not self.current_file_path or not self.files_list:
            messagebox.showinfo("Info", "Load a directory first.", parent=self.root); return
        source_entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        if not source_entities:
            messagebox.showinfo("Info", "No entities in current file to propagate.", parent=self.root); return

        # Collect unique text -> tag mappings from the current file
        text_to_tag = {}
        processed_texts = set() # Use first occurrence's tag if text appears multiple times
        # Sort by position to ensure consistency if text has multiple tags (takes first encountered)
        sorted_source = sorted(source_entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0)))
        for ann in sorted_source:
             text = ann.get('text','').strip() # Use stripped text for matching
             tag = ann.get('tag')
             if text and tag and text not in processed_texts:
                 text_to_tag[text] = tag
                 processed_texts.add(text)

        if not text_to_tag:
            messagebox.showinfo("Info", "No valid text/tag pairs found in current file to propagate.", parent=self.root); return

        confirm = messagebox.askyesno("Confirm Propagation (Current File)",
             f"Search for {len(text_to_tag)} unique text/tag pairs from '{os.path.basename(self.current_file_path)}' "
             f"across all {len(self.files_list)} files?\n\n"
             f"WARNING: Adds new entities (underlined, whitespace stripped). Skips overlaps. Relations not propagated.", parent=self.root)
        if not confirm:
            self.status_var.set("Propagation cancelled."); return
        self._perform_propagation(text_to_tag, "Current File Propagation")

    def load_and_propagate_from_dictionary(self):
        """Loads a dictionary file and propagates entities based on it."""
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
                    # Try splitting by tab first, then by last space
                    parts = line.split('\t')
                    if len(parts) != 2: parts = line.rsplit(maxsplit=1)
                    if len(parts) != 2: print(f"Warn: Bad dict line {line_num}: '{line}'"); skipped_lines += 1; continue

                    entity_text, label = parts[0].strip(), parts[1].strip()
                    if not entity_text: skipped_lines += 1; continue # Skip entries with empty text
                    # Check if the label is a currently defined entity tag
                    if label not in self.entity_tags: invalid_tags_found.add(label); skipped_lines += 1; continue
                    # Handle duplicate text entries (overwrite with the last encountered tag)
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
        confirm_msg += f"\nPropagate across {len(self.files_list)} files?\n\n(Adds entities (underlined, stripped). Skips overlaps.)"

        if not messagebox.askyesno("Confirm Dictionary Propagation", confirm_msg, parent=self.root):
            self.status_var.set("Dictionary propagation cancelled."); return
        self._perform_propagation(dictionary_mapping, "Dictionary Propagation")


    def _perform_propagation(self, text_to_tag_map, source_description):
        """ Propagates entities based on the provided map, adding 'propagated'=True,
            stripping whitespace, adjusting positions, and handling overlaps. """
        propagated_count = 0; affected_files_count = 0
        extend_option = self.extend_to_word.get(); current_file_was_modified = False
        self.status_var.set(f"Starting {source_description}..."); self.root.update_idletasks()
        # Sort texts by length (longest first) to prioritize matching longer phrases
        sorted_texts_to_find = sorted(text_to_tag_map.keys(), key=len, reverse=True)

        temp_text = tk.Text() # Use a temporary hidden Text widget for searching

        for i, file_path in enumerate(self.files_list):
            file_modified_in_this_run = False
            # Update status bar periodically
            if (i + 1) % 10 == 0 or i == len(self.files_list) - 1:
                self.status_var.set(f"{source_description}: Processing {i+1}/{len(self.files_list)}..."); self.root.update_idletasks()

            if not os.path.isfile(file_path):
                print(f"Info: Skipping missing file during propagation: {file_path}"); continue

            try:
                with open(file_path, 'r', encoding='utf-8') as f: content = f.read()
                temp_text.delete('1.0', tk.END)
                temp_text.insert('1.0', content)

                file_data = self.annotations.setdefault(file_path, {"entities": [], "relations": []})
                target_entities_list = file_data.setdefault("entities", [])
                # Create a copy for overlap checking, as we modify target_entities_list in the loop
                existing_entity_dicts_for_overlap = [e.copy() for e in target_entities_list]
                newly_added_this_file = [] # Track entities added in this file run for overlap checks

                for text_to_find in sorted_texts_to_find:
                    tag_to_apply = text_to_tag_map[text_to_find]
                    if not text_to_find: continue # Skip empty strings

                    start_index = "1.0"
                    while True:
                        # Find exact, case-sensitive match
                        found_pos_str = temp_text.search(text_to_find, start_index, stopindex=tk.END, exact=True, nocase=False)
                        if not found_pos_str: break # No more occurrences in this file

                        initial_end_pos_str = temp_text.index(f"{found_pos_str}+{len(text_to_find)}c")
                        current_match_start_pos, current_match_end_pos = found_pos_str, initial_end_pos_str

                        # Optionally extend match to whole word boundaries
                        if extend_option:
                            try:
                                # Find start of word (\M in Tcl regex)
                                word_start = temp_text.search(r"\M", current_match_start_pos, backwards=True, regexp=True)
                                # If search fails (e.g., start of line), use linestart
                                if not word_start: word_start = temp_text.index(f"{current_match_start_pos} linestart")

                                # Find end of word (\m in Tcl regex), search from char after last char of match
                                last_char_of_match = temp_text.index(f"{initial_end_pos_str}-1c")
                                word_end = temp_text.search(r"\m", f"{last_char_of_match}+1c", forwards=True, regexp=True)
                                # If search fails (e.g., end of line), use lineend
                                if not word_end: word_end = temp_text.index(f"{last_char_of_match} lineend")

                                # Update span if word boundaries differ from exact match
                                if word_start != current_match_start_pos or word_end != current_match_end_pos:
                                    current_match_start_pos, current_match_end_pos = word_start, word_end
                            except tk.TclError as e: print(f"Warn: Regex fail near {found_pos_str} in {os.path.basename(file_path)}: {e}")
                            except Exception as e: print(f"Warn: Word extension fail near {found_pos_str} in {os.path.basename(file_path)}: {e}")

                        # Get the text of the final span (potentially extended)
                        span_text = temp_text.get(current_match_start_pos, current_match_end_pos)
                        stripped_text = span_text.strip() # Final entity text is stripped
                        if not stripped_text:
                            # If span became empty after stripping, skip and advance search
                            start_index = initial_end_pos_str
                            continue

                        # Calculate adjusted start/end indices based on stripped text
                        leading_ws = len(span_text) - len(span_text.lstrip())
                        adj_start_pos_str = temp_text.index(f"{current_match_start_pos}+{leading_ws}c")
                        # End position is start + length of stripped text
                        adj_end_pos_str = temp_text.index(f"{adj_start_pos_str}+{len(stripped_text)}c")

                        try:
                            adj_sl, adj_sc = map(int, adj_start_pos_str.split('.'))
                            adj_el, adj_ec = map(int, adj_end_pos_str.split('.'))
                        except ValueError:
                            print(f"Error parsing adjusted positions during propagation: {adj_start_pos_str}/{adj_end_pos_str} in {os.path.basename(file_path)}")
                            start_index = initial_end_pos_str # Advance search past this problematic match
                            continue

                        # Check for overlap with existing entities *before* this propagation run
                        overlap = self._is_overlapping_in_list(adj_sl, adj_sc, adj_el, adj_ec, existing_entity_dicts_for_overlap)
                        # Check for overlap with entities *newly added* in this file during *this* propagation run
                        if not overlap:
                           overlap = self._is_overlapping_in_list(adj_sl, adj_sc, adj_el, adj_ec, newly_added_this_file)


                        # If no overlap detected with existing or newly added entities
                        if not overlap:
                            entity_id = uuid.uuid4().hex
                            new_annotation = {'id': entity_id, 'start_line': adj_sl, 'start_char': adj_sc,
                                              'end_line': adj_el, 'end_char': adj_ec, 'text': stripped_text,
                                              'tag': tag_to_apply, 'propagated': True} # Mark as propagated
                            target_entities_list.append(new_annotation)
                            newly_added_this_file.append(new_annotation) # Add to list for overlap check within this file
                            propagated_count += 1
                            file_modified_in_this_run = True
                            if file_path == self.current_file_path: current_file_was_modified = True

                        # Advance search index to the end of the original match found
                        start_index = initial_end_pos_str

            except Exception as e: print(f"ERROR processing '{os.path.basename(file_path)}' during propagation:\n{str(e)}")

            if file_modified_in_this_run: affected_files_count += 1

        temp_text.destroy() # Clean up temporary widget

        # If the currently viewed file was modified, refresh the UI
        if current_file_was_modified:
            self.update_entities_list()
            self.apply_annotations_to_text()
        self._update_button_states() # Update buttons in case propagate button needs disabling etc.

        summary = f"{source_description} complete.\nAdded {propagated_count} entities across {affected_files_count} files."
        if extend_option: summary += "\n('Extend to whole word' was enabled)"
        messagebox.showinfo("Propagation Results", summary, parent=self.root)
        self.status_var.set(f"{source_description} finished. Added {propagated_count} entities.")


    # --- Tag/Type Management ---
    def _manage_items(self, item_type_name, current_items_list, update_combobox_func):
        """Generic modal window for managing tags/types."""
        window = tk.Toplevel(self.root); window.title(f"Manage {item_type_name}")
        window.geometry("350x400"); window.minsize(300, 250)
        window.transient(self.root); window.grab_set()

        list_frame = tk.Frame(window); list_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(10, 0))
        tk.Label(list_frame, text=f"Current {item_type_name}:").pack(anchor=tk.W)
        scrollbar = tk.Scrollbar(list_frame); scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        listbox = tk.Listbox(list_frame, yscrollcommand=scrollbar.set, exportselection=False, selectmode=tk.EXTENDED)

        current_items_list.sort(key=str.lower) # Sort case-insensitively for display
        for item in current_items_list:
            listbox.insert(tk.END, item)
            # Apply background color for entity tags
            if item_type_name == "Entity Tags":
                try: listbox.itemconfig(tk.END, {'bg': self.get_color_for_tag(item)})
                except tk.TclError: pass # Ignore if color cannot be applied

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
                    # Re-sort the listbox after adding
                    items = list(listbox.get(0, tk.END)); items.sort(key=str.lower)
                    listbox.delete(0, tk.END)
                    for i in items:
                        listbox.insert(tk.END, i)
                        # Re-apply color if it's an entity tag
                        if item_type_name == "Entity Tags":
                            try: listbox.itemconfig(tk.END, {'bg': self.get_color_for_tag(i)})
                            except tk.TclError: pass
                    item_var.set(""); listbox.see(tk.END) # Clear entry and scroll to end
                else: messagebox.showwarning("Duplicate", f"'{item}' already exists.", parent=window)
            item_entry.focus_set() # Return focus to entry

        item_entry.bind("<Return>", lambda event: add_item()) # Allow adding with Enter key
        add_btn = tk.Button(controls_frame, text="Add", width=7, command=add_item)
        add_btn.grid(row=0, column=1, padx=5)

        def remove_item():
            indices = listbox.curselection()
            if indices:
                items_to_remove = [listbox.get(i) for i in indices]
                # Check if removing Entity Tags that are currently in use
                if item_type_name == "Entity Tags":
                    tags_in_use = set()
                    for data in self.annotations.values():
                         for entity in data.get("entities", []):
                             if entity.get('tag') in items_to_remove:
                                 tags_in_use.add(entity.get('tag'))
                    if tags_in_use:
                        if not messagebox.askyesno("Confirm Tag Removal",
                            f"The following tags are used by existing annotations:\n- {', '.join(tags_in_use)}\n\nRemove anyway? (Annotations will lose their tag and color)", parent=window): return
                # Remove selected items from listbox (iterate reversed indices)
                for index in sorted(indices, reverse=True):
                    listbox.delete(index)
            else: messagebox.showwarning("No Selection", "Select item(s) to remove.", parent=window)

        remove_btn = tk.Button(controls_frame, text="Remove", width=7, command=remove_item)
        remove_btn.grid(row=0, column=2)

        button_frame = tk.Frame(window); button_frame.pack(fill=tk.X, padx=10, pady=(5, 10))
        def save_changes():
            new_items = list(listbox.get(0, tk.END))
            # Check if changes were actually made
            if set(new_items) != set(current_items_list):
                removed = set(current_items_list) - set(new_items)
                added = set(new_items) - set(current_items_list)
                # Update the main application list
                current_items_list[:] = new_items
                update_combobox_func() # Update the dropdown menu
                # Special handling for Entity Tags
                if item_type_name == "Entity Tags":
                    for tag in added: self.get_color_for_tag(tag) # Assign new colors
                    self._configure_text_tags() # Reconfigure tags in text area
                    # Remove deleted tags from text area and color map
                    for tag in removed:
                        try: self.text_area.tag_delete(tag)
                        except tk.TclError: pass
                        if tag in self.tag_colors: del self.tag_colors[tag]
                    # Re-apply highlights and update lists to reflect tag changes/removals
                    self.apply_annotations_to_text(); self.update_entities_list()
                # Update relations list if relation types changed (display might change)
                elif item_type_name == "Relation Types": self.update_relations_list()
                self.status_var.set(f"{item_type_name} updated.")
            else:
                self.status_var.set(f"No changes made to {item_type_name}.")
            window.destroy()

        save_btn = tk.Button(button_frame, text="Save Changes", width=12, command=save_changes)
        save_btn.pack(side=tk.RIGHT, padx=5)
        cancel_btn = tk.Button(button_frame, text="Cancel", width=12, command=window.destroy)
        cancel_btn.pack(side=tk.RIGHT)
        item_entry.focus_set(); window.wait_window() # Wait for modal to close


    def manage_entity_tags(self):
        """Opens the modal window to manage entity tags."""
        self._manage_items("Entity Tags", self.entity_tags, self._update_entity_tag_combobox)

    def manage_relation_types(self):
        """Opens the modal window to manage relation types."""
        self._manage_items("Relation Types", self.relation_types, self._update_relation_type_combobox)


# --- Main Execution ---
def main():
    root = tk.Tk()
    try: # Apply theme if possible
        style = ttk.Style()
        themes = style.theme_names()
        # Prefer more modern themes if available
        for t in ['clam', 'alt', 'vista', 'xpnative', 'default']:
            if t in themes: style.theme_use(t); break
    except tk.TclError: print("ttk themes not available or failed.")

    app = TextAnnotator(root)
    root.mainloop()

if __name__ == "__main__":
    main()
