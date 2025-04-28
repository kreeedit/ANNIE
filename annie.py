# -*- coding: utf-8 -*-
"""
ANNIE: Annotation Interface for Named-entity & Information Extraction.
# ... (rest of the docstring) ...
Adds underlining for propagated entities.
Fixes whitespace issues in propagated entities (saving & underlining).
"""

import os
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import json
from pathlib import Path
import uuid  # For unique IDs
import itertools # For cycling through colors
import re # For word boundary checking if needed

# --- Constants ---
SESSION_FILE_VERSION = "1.6" # Incremented version for propagation whitespace fix

# ... (Keep the rest of the class __init__ and other methods as they were in the previous version) ...
# Make sure __init__, create_menu, create_layout, _configure_text_tags, etc., are unchanged
# from the version that included underlining.

class TextAnnotator:
    """
    Main application class
    Handles UI creation, file loading, annotation logic, and saving.
    """
    def __init__(self, root_window):
        """
        Initializes the application.
        Sets up variables, colors, and builds the UI.
        """
        self.root = root_window
        self.root.title("ANNIE - Annotation Interface") # Shortened title
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
        self.create_layout()

        # --- Status Bar ---
        self.status_var = tk.StringVar(value="Ready. Open a directory or load a session.")
        self.status_bar = tk.Label(self.root, textvariable=self.status_var, bd=1, relief=tk.SUNKEN, anchor=tk.W)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)

        # --- Initial UI Setup ---
        self._update_entity_tag_combobox()
        self._update_relation_type_combobox()
        self._configure_text_tags() # <-- Configures entity background AND propagated underline tags
        self._configure_treeview_tags()
        self._update_button_states()

        # --- Add protocol for closing window ---
        self.root.protocol("WM_DELETE_WINDOW", self._on_closing)


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
        file_menu.add_command(label="Save Session As...", command=lambda: self.save_session(force_ask=True)) # Force save dialog
        file_menu.add_separator()
        # --- End ---
        file_menu.add_command(label="Save Annotations Only...", command=self.save_annotations) # Renamed for clarity
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self._on_closing) # Use closing handler
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
            undo=True, state=tk.DISABLED,
            borderwidth=1, relief="sunken"
        )
        self.text_area.pack(fill=tk.BOTH, expand=True)
        scrollbar_text_y.config(command=self.text_area.yview)
        scrollbar_text_x.config(command=self.text_area.xview)

        # --- ADD BINDING FOR RIGHT-CLICK ---
        # Use platform-specific right-click event
        self.text_area.bind("<Button-3>", self._on_text_right_click) # Button-3 for Windows/Linux
        self.text_area.bind("<Button-2>", self._on_text_right_click) # Button-2 for macOS (often)
        # --- END ADD BINDING ---


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
        self.annotate_btn = tk.Button(ecf_top, text="Annotate", command=self.annotate_selection, state=tk.DISABLED, width=8)
        self.annotate_btn.pack(side=tk.LEFT, padx=5)
        self.remove_entity_btn = tk.Button(ecf_top, text="Remove", command=self.remove_entity_annotation, state=tk.DISABLED, width=8)
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
        # Get the character, ensure it's printable
        if not event.char or not event.char.isprintable() or len(event.char) != 1:
            return  # Let the event propagate for regular navigation keys

        char = event.char.lower()

        # Get all items in current sorted order
        all_items = tree.get_children("")
        if not all_items:
            return  # Empty tree

        # Get currently focused item index
        focused_item = tree.focus()
        current_idx = -1
        if focused_item and focused_item in all_items: # Check if focus item exists
            try:
                current_idx = all_items.index(focused_item)
            except ValueError:
                current_idx = -1

        # Determine which column to use for filtering (Text column for entities, Head for relations)
        if tree == self.entities_tree:
            match_column = "Text"
        else:  # relations_tree
            match_column = "Head"

        # Start searching from the item after the current one
        start_idx = (current_idx + 1) % len(all_items) if current_idx >= 0 else 0

        # Search for an item starting with the pressed key
        found_idx = None

        # Search from current position to end
        for i in range(start_idx, len(all_items)):
            item_id = all_items[i]
            item_text = str(tree.set(item_id, match_column)).lower()
            if item_text.startswith(char):
                found_idx = i
                break

        # If not found, wrap around to beginning
        if found_idx is None:
            for i in range(0, start_idx):
                item_id = all_items[i]
                item_text = str(tree.set(item_id, match_column)).lower()
                if item_text.startswith(char):
                    found_idx = i
                    break

        # If found, select and focus on it
        if found_idx is not None:
            found_item = all_items[found_idx]
            # Use selection_set for multi-select treeview as well
            tree.selection_set(found_item) # Replace current selection
            tree.focus(found_item)
            tree.see(found_item)
            # Trigger selection event programmatically to update highlights/buttons
            if tree == self.entities_tree:
                self.on_entity_select(None)
            else:
                self.on_relation_select(None)
            return "break"  # Stop event propagation

    # --- Color and Tag Configuration ---
    def get_color_for_tag(self, tag):
        """Gets a color for a tag, generating one if not predefined."""
        if tag not in self.tag_colors:
            try:
                # Ensure the tag exists in the official list before assigning color
                if tag in self.entity_tags:
                    self.tag_colors[tag] = next(self.color_cycle)
                else:
                    # Handle case where tag might be requested but not officially managed (e.g., old data)
                    return "#cccccc" # Default grey
            except Exception:
                self.tag_colors[tag] = "#cccccc" # Fallback if cycle fails
        return self.tag_colors.get(tag, "#cccccc") # Default grey if lookup fails

    def _configure_text_tags(self):
        """Configures background colors for entity tags and underline for propagated."""
        # Configure standard entity tags with background colors
        for tag in self.entity_tags:
            color = self.get_color_for_tag(tag)
            try:
                # Explicitly set underline to False for standard tags
                # to prevent accidental inheritance or overrides.
                self.text_area.tag_configure(tag, background=color, underline=False)
            except tk.TclError as e:
                print(f"Warning: Could not configure text tag '{tag}': {e}")

        # Configure the specific tag for underlining propagated entities
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
                font=('TkDefaultFont', 9, 'italic') # Use default font but modify style
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
            # If current selection is no longer valid or combobox was disabled, set to first
            if current_selection not in self.entity_tags or self.entity_tag_combobox['state'] == tk.DISABLED:
                if self.entity_tags: # Ensure list is not empty
                    self.selected_entity_tag.set(self.entity_tags[0])
                else:
                     self.selected_entity_tag.set("")
            else:
                # Ensure current selection remains if still valid
                self.selected_entity_tag.set(current_selection)
            self.entity_tag_combobox.config(state="readonly" if self.entity_tags else tk.DISABLED)

    def _update_relation_type_combobox(self):
        """Updates the values and state of the relation type combobox."""
        current_selection = self.selected_relation_type.get()
        if not self.relation_types:
            self.selected_relation_type.set("")
            self.relation_type_combobox.config(values=[], state=tk.DISABLED)
        else:
            self.relation_type_combobox['values'] = self.relation_types
            if current_selection not in self.relation_types or self.relation_type_combobox['state'] == tk.DISABLED:
                if self.relation_types: # Ensure list is not empty
                    self.selected_relation_type.set(self.relation_types[0])
                else:
                    self.selected_relation_type.set("")
            else:
                self.selected_relation_type.set(current_selection)
            self.relation_type_combobox.config(state="readonly" if self.relation_types else tk.DISABLED)

    # --- Button State Management ---
    def _update_button_states(self):
        """Enable/disable buttons based on current application state."""
        file_loaded = bool(self.current_file_path)
        has_files = bool(self.files_list)
        num_entities_selected = len(self.entities_tree.selection()) # Number of selected *rows*
        num_relations_selected = len(self.relations_tree.selection())

        # File Navigation
        self.prev_btn.config(state=tk.NORMAL if has_files and self.current_file_index > 0 else tk.DISABLED)
        self.next_btn.config(state=tk.NORMAL if has_files and self.current_file_index < len(self.files_list) - 1 else tk.DISABLED)

        # Text Area
        self.text_area.config(state=tk.NORMAL if file_loaded else tk.DISABLED)

        # Entity Buttons
        can_annotate_entity = file_loaded and self.entity_tags and self.text_area.cget('state') == tk.NORMAL
        self.annotate_btn.config(state=tk.NORMAL if can_annotate_entity else tk.DISABLED)
        self.remove_entity_btn.config(state=tk.NORMAL if num_entities_selected > 0 else tk.DISABLED)
        self.merge_entities_btn.config(state=tk.NORMAL if num_entities_selected >= 2 else tk.DISABLED)
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
        # Check for unsaved changes before discarding current state
        if self._has_unsaved_changes():
            if not messagebox.askyesno("Unsaved Changes", "You have unsaved changes in the current session.\nDiscard changes and load new directory?", parent=self.root):
                return # User cancelled

        directory = filedialog.askdirectory(title="Select Directory with Text Files")
        if directory:
            new_files_list = []
            try:
                # Scan for .txt files
                for filename in sorted(os.listdir(directory)):
                    if filename.lower().endswith(".txt"):
                        full_path = os.path.join(directory, filename)
                        # Basic check if it's actually a file
                        if os.path.isfile(full_path):
                            new_files_list.append(full_path)

            except OSError as e:
                messagebox.showerror("Error Loading Directory", f"Could not read directory contents:\n{e}")
                return # Stop if directory cannot be read

            if new_files_list:
                # Reset application state *after* successfully scanning
                self._reset_state() # Clear annotations, paths, etc.
                self.files_list = new_files_list
                self.session_save_path = None # New directory means it's not the previously saved session

                # Populate the listbox
                self.files_listbox.delete(0, tk.END)
                for file_path in self.files_list:
                    self.files_listbox.insert(tk.END, os.path.basename(file_path))

                self.load_file(0) # Load the first file
                self.status_var.set(f"Loaded {len(self.files_list)} files from '{os.path.basename(directory)}'")
                # Set title to reflect directory
                self.root.title(f"ANNIE - {os.path.basename(directory)}")
            else:
                 # If no text files found, don't reset the state, just inform the user
                self.status_var.set(f"No .txt files found in '{os.path.basename(directory)}'")
                self.files_listbox.delete(0, tk.END) # Clear listbox if no files found

            self._update_button_states()

    def load_file(self, index):
        """Loads the content and annotations for the file at the given index."""
        if not (0 <= index < len(self.files_list)):
            print(f"Warning: Invalid file index {index} requested.")
            return

        # Check if index is actually changing
        if index == self.current_file_index and self.current_file_path:
            # print("Debug: Same file index selected, no reload.")
            return

        # Clear views *before* loading new content
        self.clear_views() # Clears text, treeviews, selection state

        self.current_file_index = index
        self.current_file_path = self.files_list[index]
        filename = os.path.basename(self.current_file_path)

        # Update listbox selection visually
        self.files_listbox.selection_clear(0, tk.END)
        self.files_listbox.selection_set(index)
        self.files_listbox.activate(index) # Visually indicates the active item
        self.files_listbox.see(index) # Ensure selected item is visible

        # Load file content
        self.text_area.config(state=tk.NORMAL) # Temporarily enable to insert text
        self.text_area.delete(1.0, tk.END)
        file_loaded_successfully = False
        try:
            with open(self.current_file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                self.text_area.insert(tk.END, content)
            file_loaded_successfully = True
        except Exception as e:
            messagebox.showerror("Error Reading File", f"Failed to load file '{filename}':\n{str(e)}")
            self.text_area.config(state=tk.DISABLED)
            # Mark file as problematic? Clear current file info?
            self.current_file_path = None # Consider this problematic now
            self.status_var.set(f"Error loading {filename}")
            file_loaded_successfully = False
            # Clear annotation lists as well if file fails to load
            try: self.entities_tree.delete(*self.entities_tree.get_children())
            except Exception: pass
            try: self.relations_tree.delete(*self.relations_tree.get_children())
            except Exception: pass
            self.selected_entity_ids_for_relation = []


        # If loaded successfully, load/apply annotations
        if file_loaded_successfully:
            # Ensure annotations structure exists for this file
            file_data = self.annotations.setdefault(self.current_file_path, {"entities": [], "relations": []})
            file_data.setdefault("entities", [])
            file_data.setdefault("relations", [])

            # Populate UI lists and apply highlighting
            self.update_entities_list() # Must happen before relation list if using entity text map
            self.update_relations_list()
            self.apply_annotations_to_text() # Highlight entities in text (handles propagated underline)

            self.status_var.set(f"Loaded: {filename} ({index+1}/{len(self.files_list)})")

            # Reset undo stack for the new file
            self.text_area.edit_reset()
            self.text_area.config(state=tk.NORMAL) # Ensure editable

        # Always update button states after load attempt
        self._update_button_states()

    def clear_views(self):
        """Clears text area content, highlights, and annotation list Treeviews."""
        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL) # Enable to modify
        self.text_area.delete(1.0, tk.END)
        # Remove all known entity tag highlights AND propagated underline tag
        current_text_tags = list(self.text_area.tag_names())
        tags_to_remove = set(self.entity_tags)
        tags_to_remove.add("propagated_entity")

        for tag_name in current_text_tags:
            if tag_name in tags_to_remove and tag_name != tk.SEL: # Don't remove selection tag
                try:
                    self.text_area.tag_remove(tag_name, "1.0", tk.END)
                except tk.TclError: pass # Ignore if tag doesn't exist

        # Remove selection highlight specifically
        try:
            self.text_area.tag_remove(tk.SEL, "1.0", tk.END)
        except tk.TclError: pass

        # Restore original state (usually DISABLED if no file was loaded, NORMAL if file was loaded)
        self.text_area.config(state=original_state if self.current_file_path else tk.DISABLED)

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
        # Keep entity tags, relation types, colors as they are user settings, not session-specific unless loaded
        self.session_save_path = None # Reset session path
        self.root.title("ANNIE - Annotation Interface") # Reset title
        self.status_var.set("Ready. Open a directory or load a session.")


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
            # Load only if the selection changed to a different file index
            if index != self.current_file_index:
                self.load_file(index)

    # --- Annotation Saving (Annotations ONLY) ---
    def save_annotations(self):
        """Saves ONLY annotations (entities/relations) for all files to a JSON file."""
        if not self.annotations or all(not data.get('entities') and not data.get('relations') for data in self.annotations.values()):
            messagebox.showinfo("Info", "There are no annotations to save.", parent=self.root)
            return

        # Suggest save location based on the first file's directory
        initial_dir = os.path.dirname(self.files_list[0]) if self.files_list else ""
        initial_file = "annotations_only.json"
        if initial_dir:
            dir_name = os.path.basename(initial_dir)
            if dir_name: initial_file = f"{dir_name}_annotations_only.json"

        save_path = filedialog.asksaveasfilename(
            initialdir=initial_dir,
            initialfile=initial_file,
            defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
            title="Save Annotations ONLY As",
            parent=self.root
        )

        if not save_path:
            self.status_var.set("Save annotations cancelled.")
            return

        # Prepare data: Use relative paths if possible, relative to the SAVE location
        save_dir = os.path.dirname(save_path)
        serializable_annotations = {}

        for file_path, data in self.annotations.items():
            entities = data.get("entities", [])
            relations = data.get("relations", [])
            if not entities and not relations: continue # Skip empty

            key = file_path # Default to full path
            try:
                # Make path relative to the *save* directory if possible
                rel_path = os.path.relpath(file_path, start=save_dir)
                # Using Pathlib for a slightly more robust check if available
                use_rel_path = False
                try:
                    if Path(file_path).is_relative_to(save_dir): # Requires Python 3.9+
                        use_rel_path = True
                except AttributeError: # Fallback for older Python
                     if not os.path.isabs(rel_path) and not rel_path.startswith(('..'+os.sep, '..'+'/')):
                         use_rel_path = True

                if use_rel_path:
                     key = rel_path.replace('\\', '/') # Use forward slashes
                else: # Fallback to basename if it seems outside the save hierarchy
                    key = os.path.basename(file_path)
            except ValueError: # Handle different drives on Windows
                key = os.path.basename(file_path)
            except Exception as e:
                print(f"Warning: Error calculating relative path for {file_path} relative to {save_dir}. Using basename. Error: {e}")
                key = os.path.basename(file_path)

            # Sort annotations for consistent output
            # Keep the propagated flag when saving
            sorted_entities = sorted(entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0)))
            sorted_relations = sorted(relations, key=lambda r: (r.get('type', ''), r.get('head_id','')))

            serializable_annotations[key] = {
                "entities": sorted_entities,
                "relations": sorted_relations
            }

        # Write to JSON
        try:
            with open(save_path, 'w', encoding='utf-8') as f:
                json.dump(serializable_annotations, f, indent=2, ensure_ascii=False)
            self.status_var.set(f"Annotations ONLY saved to '{os.path.basename(save_path)}'")
        except Exception as e:
            messagebox.showerror("Save Error", f"Could not write annotations to file:\n{e}", parent=self.root)
            self.status_var.set("Error saving annotations.")


    # --- Session Save/Load ---
    def save_session(self, force_ask=False):
        """Saves the entire application state (files, annotations, settings) to a session file."""
        if not self.files_list:
            messagebox.showwarning("Cannot Save Session", "Please open a directory first.", parent=self.root)
            return

        save_path = self.session_save_path
        if force_ask or not save_path:
            # Suggest save location based on the first file's directory
            initial_dir = os.path.dirname(self.files_list[0]) if self.files_list else ""
            initial_file = "annie_session.json"
            if initial_dir:
                dir_name = os.path.basename(initial_dir)
                if dir_name: initial_file = f"{dir_name}_session.json"

            save_path = filedialog.asksaveasfilename(
                initialdir=initial_dir,
                initialfile=initial_file,
                defaultextension=".json",
                filetypes=[("ANNIE Session files", "*.json"), ("All files", "*.*")],
                title="Save Session As",
                parent=self.root
            )

        if not save_path:
            self.status_var.set("Save session cancelled.")
            return

        # Prepare session data (annotations will include 'propagated' flag if present)
        session_data = {
            "version": SESSION_FILE_VERSION,
            "files_list": self.files_list, # Store full paths
            "current_file_index": self.current_file_index,
            "entity_tags": self.entity_tags,
            "relation_types": self.relation_types,
            "tag_colors": self.tag_colors,
            "annotations": self.annotations, # Store with full paths as keys
            "extend_to_word": self.extend_to_word.get() # Save propagation setting
        }

        # Write to JSON file
        try:
            with open(save_path, 'w', encoding='utf-8') as f:
                json.dump(session_data, f, indent=2, ensure_ascii=False)
            self.session_save_path = save_path # Remember path for next quick save
            self.status_var.set(f"Session saved to '{os.path.basename(save_path)}'")
            # Update title to show session name
            base_dir_name = "Session"
            if self.files_list:
                try: base_dir_name = os.path.basename(os.path.dirname(self.files_list[0]))
                except: pass
            self.root.title(f"ANNIE - {base_dir_name} [{os.path.basename(save_path)}]")
        except Exception as e:
            messagebox.showerror("Save Session Error", f"Could not write session file:\n{e}", parent=self.root)
            self.status_var.set("Error saving session.")
            self.session_save_path = None # Failed, clear path

    def load_session(self):
        """Loads application state from a session file."""
        # Check for unsaved changes before discarding current state
        if self._has_unsaved_changes():
            if not messagebox.askyesno("Unsaved Changes", "You have unsaved changes in the current session.\nDiscard changes and load session?", parent=self.root):
                return # User cancelled

        load_path = filedialog.askopenfilename(
            defaultextension=".json",
            filetypes=[("ANNIE Session files", "*.json"), ("All files", "*.*")],
            title="Load Session",
            parent=self.root
        )

        if not load_path:
            self.status_var.set("Load session cancelled.")
            return

        # Read and parse JSON
        try:
            with open(load_path, 'r', encoding='utf-8') as f:
                session_data = json.load(f)
        except FileNotFoundError:
            messagebox.showerror("Load Session Error", f"File not found:\n{load_path}", parent=self.root)
            return
        except json.JSONDecodeError as e:
            messagebox.showerror("Load Session Error", f"Invalid session file format (JSON Error):\n{e}", parent=self.root)
            return
        except Exception as e:
            messagebox.showerror("Load Session Error", f"Could not read session file:\n{e}", parent=self.root)
            return

        # --- Basic Validation ---
        required_keys = ["version", "files_list", "current_file_index",
                         "entity_tags", "relation_types", "tag_colors", "annotations"]
        optional_keys = ["extend_to_word"] # Keys that might be missing in older versions
        missing_required = [k for k in required_keys if k not in session_data]

        if missing_required:
             messagebox.showerror("Load Session Error", f"Session file is missing required data: {', '.join(missing_required)}", parent=self.root)
             return

        # Basic type checking
        type_errors = []
        if not isinstance(session_data.get("files_list"), list): type_errors.append("files_list not list")
        if not isinstance(session_data.get("current_file_index"), int): type_errors.append("current_file_index not int")
        if not isinstance(session_data.get("annotations"), dict): type_errors.append("annotations not dict")
        if not isinstance(session_data.get("entity_tags"), list): type_errors.append("entity_tags not list")
        if not isinstance(session_data.get("relation_types"), list): type_errors.append("relation_types not list")
        if not isinstance(session_data.get("tag_colors"), dict): type_errors.append("tag_colors not dict")
        if "extend_to_word" in session_data and not isinstance(session_data.get("extend_to_word"), bool):
             type_errors.append("extend_to_word not bool")

        if type_errors:
            messagebox.showerror("Load Session Error", f"Session file contains data with incorrect types: {', '.join(type_errors)}.", parent=self.root)
            return

        # Version check (example)
        loaded_version = session_data.get("version", "0.0")
        # print(f"Loading session version: {loaded_version}") # For debug
        # Add compatibility checks or warnings if needed based on loaded_version

        # --- Check if text files still exist ---
        loaded_files_list = session_data["files_list"]
        missing_files = [fp for fp in loaded_files_list if not os.path.isfile(fp)]
        if missing_files:
            msg = f"Some text files referenced in the session could not be found:\n"
            msg += "\n".join([f"- {os.path.basename(mf)} ({os.path.dirname(mf)})" for mf in missing_files[:5]])
            if len(missing_files) > 5: msg += "\n..."
            msg += "\n\nContinue loading session? Annotations for missing files will be kept but files cannot be displayed."
            if not messagebox.askyesno("Missing Files", msg, parent=self.root):
                self.status_var.set("Load session cancelled due to missing files.")
                return

        # --- Restore State ---
        self._reset_state() # Clear current state *before* loading new

        try:
            self.files_list = loaded_files_list
            self.current_file_index = session_data["current_file_index"]
            self.annotations = session_data["annotations"] # Includes 'propagated' flag if saved
            self.entity_tags = session_data["entity_tags"]
            self.relation_types = session_data["relation_types"]
            self.tag_colors = session_data["tag_colors"]
            self.extend_to_word.set(session_data.get("extend_to_word", False)) # Load setting, default false if missing

            self.session_save_path = load_path # Remember loaded session path

            # --- Update UI ---
            self.files_listbox.delete(0, tk.END)
            for file_path in self.files_list:
                # Indicate missing files in the listbox
                display_name = os.path.basename(file_path)
                if file_path in missing_files:
                    display_name += " [MISSING]"
                self.files_listbox.insert(tk.END, display_name)

            # Validate current_file_index
            if not (0 <= self.current_file_index < len(self.files_list)):
                 messagebox.showwarning("Load Session Warning", "Saved file index is out of bounds. Loading first file instead.", parent=self.root)
                 self.current_file_index = 0 if self.files_list else -1

            # Update settings UI elements
            self._update_entity_tag_combobox()
            self._update_relation_type_combobox()
            self._configure_text_tags() # Apply loaded colors AND ensure propagated tag exists
            self._configure_treeview_tags() # Ensure treeview styles are set

            # Load the correct file (if index is valid and file exists)
            if self.current_file_index != -1:
                 # Check if the target file is missing before attempting to load
                if self.files_list[self.current_file_index] in missing_files:
                    self.status_var.set(f"Session loaded. Current file '{os.path.basename(self.files_list[self.current_file_index])}' is missing.")
                    self.clear_views() # Clear text area etc. as file can't be shown
                    # Visually select in listbox
                    self.files_listbox.selection_clear(0, tk.END)
                    self.files_listbox.selection_set(self.current_file_index)
                    self.files_listbox.activate(self.current_file_index)
                    self.files_listbox.see(self.current_file_index)
                    self._update_button_states() # Update buttons (text area will be disabled)
                else:
                    # Force load even if index seems the same initially after reset
                    current_idx_temp = self.current_file_index
                    self.current_file_index = -1 # Trick load_file into thinking index changed
                    self.load_file(current_idx_temp)
            else:
                # No files in list or invalid index after load
                self.status_var.set("Session loaded, but no files to display.")
                self.clear_views()
                self._update_button_states()

            # Update window title
            base_dir_name = "Session"
            if self.files_list:
                try: base_dir_name = os.path.basename(os.path.dirname(self.files_list[0]))
                except: pass # Ignore errors getting dirname
            self.root.title(f"ANNIE - {base_dir_name} [{os.path.basename(load_path)}]")

        except Exception as e:
            # Catch unexpected errors during state restoration
            messagebox.showerror("Load Session Error", f"An error occurred while applying session data:\n{e}", parent=self.root)
            self._reset_state() # Attempt to reset to a clean state
            self._update_button_states()


    # --- Check for Unsaved Changes ---
    def _has_unsaved_changes(self):
        """Checks if there are potential unsaved changes in the current session."""
        # This is a simple check. A more robust check would compare the current state
        # to the state when the session was last saved or loaded (needs storing hash/timestamp).
        # For now, just check if there are any files loaded, implying potential work.
        return bool(self.files_list) # Returns True if a directory/session is loaded

    def _on_closing(self):
        """Handles the window close event."""
        if self._has_unsaved_changes():
            response = messagebox.askyesnocancel("Exit Confirmation", "You have an active session.\nSave session before exiting?", parent=self.root)
            if response is True: # Yes, save
                self.save_session()
                # Quit regardless of whether save succeeded or was cancelled by user
                self.root.quit()
            elif response is False: # No, don't save
                 self.root.quit()
            # else: # Cancel (response is None) - do nothing
        else:
            # No unsaved changes detected
            self.root.quit()


    # --- Entity Annotation ---
    # Helper functions for overlap checking
    def _spans_overlap_numeric(self, start1_line, start1_char, end1_line, end1_char,
                                     start2_line, start2_char, end2_line, end2_char):
        """Checks if two spans, defined by line/char numbers, overlap."""
        # Normalize spans (start should be <= end)
        span1_start = (start1_line, start1_char)
        span1_end = (end1_line, end1_char)
        span2_start = (start2_line, start2_char)
        span2_end = (end2_line, end2_char)
        # Basic validation
        if span1_start > span1_end: span1_start, span1_end = span1_end, span1_start
        if span2_start > span2_end: span2_start, span2_end = span2_end, span2_start

        # Check for non-overlap: span1 ends strictly before span2 starts OR span1 starts strictly after span2 ends
        # Tkinter index logic: '1.5' is the 5th char on line 1. A span '1.0' to '1.5' includes 5 chars.
        # The end index is exclusive for ranges/tags.
        # Overlap occurs if NOT (span1_end <= span2_start OR span1_start >= span2_end)
        is_disjoint = (span1_end <= span2_start) or (span1_start >= span2_end)
        return not is_disjoint

    def _is_overlapping_in_list(self, start_line, start_char, end_line, end_char, existing_entities_list):
        """Checks if the given span overlaps with any entity dict in the provided list."""
        for ann in existing_entities_list:
            if not all(k in ann for k in ['start_line', 'start_char', 'end_line', 'end_char']):
                print(f"Warning: Skipping overlap check against entity {ann.get('id','N/A')} missing position.")
                continue
            if self._spans_overlap_numeric(
                start_line, start_char, end_line, end_char,
                ann['start_line'], ann['start_char'], ann['end_line'], ann['end_char']
            ):
                # print(f"Debug: Overlap detected between ({start_line}.{start_char}-{end_line}.{end_char}) and existing ({ann['start_line']}.{ann['start_char']}-{ann['end_line']}.{ann['end_char']})")
                return True # Overlap found
        return False # No overlap found

    # --- Entity Annotation (Manual) ---
    def annotate_selection(self):
        """Annotates the selected text in the text_area as an entity."""
        if not self.current_file_path or self.text_area.cget('state') == tk.DISABLED:
            messagebox.showinfo("Info", "Please load a file and ensure text area is active.", parent=self.root)
            return
        if not self.entity_tags:
            messagebox.showwarning("Warning", "No entity tags defined.", parent=self.root)
            return

        try:
            start_pos = self.text_area.index(tk.SEL_FIRST)
            end_pos = self.text_area.index(tk.SEL_LAST)
            selected_text = self.text_area.get(start_pos, end_pos)

            if not selected_text.strip():
                messagebox.showinfo("Info", "No text selected or selection is only whitespace.", parent=self.root)
                return

            # --- Adjust selection to remove leading/trailing whitespace ---
            adj_start_pos = start_pos
            adj_end_pos = end_pos
            adj_selected_text = selected_text

            leading_whitespace = len(selected_text) - len(selected_text.lstrip())
            trailing_whitespace = len(selected_text) - len(selected_text.rstrip())

            if leading_whitespace > 0:
                adj_start_pos = self.text_area.index(f"{start_pos}+{leading_whitespace}c")
            if trailing_whitespace > 0:
                 adj_end_pos = self.text_area.index(f"{end_pos}-{trailing_whitespace}c")

            # Get the final stripped text based on adjusted positions
            if leading_whitespace > 0 or trailing_whitespace > 0:
                adj_selected_text = self.text_area.get(adj_start_pos, adj_end_pos)
                # Double check if stripping the retrieved text changes it further (unlikely but safe)
                if adj_selected_text.strip() != adj_selected_text:
                     print("Warning: Whitespace adjustment issue during manual annotation.")
                     # Fallback to original selection if adjustment fails badly
                     adj_start_pos = start_pos
                     adj_end_pos = end_pos
                     adj_selected_text = selected_text.strip() # Save at least stripped
                     if not adj_selected_text: return # Don't annotate if only whitespace remains
                elif not adj_selected_text: # If selection was only whitespace
                     messagebox.showinfo("Info", "Selection is only whitespace.", parent=self.root)
                     return

            start_line, start_char = map(int, adj_start_pos.split('.'))
            end_line, end_char = map(int, adj_end_pos.split('.'))
            final_text = adj_selected_text # Use the potentially adjusted, stripped text
            # --- End Whitespace Adjustment ---


            tag = self.selected_entity_tag.get()
            if not tag:
                messagebox.showwarning("Warning", "No entity tag selected.", parent=self.root)
                return

            # Check for overlap using the *adjusted* positions
            entities_in_file = self.annotations.get(self.current_file_path, {}).get("entities", [])
            if self._is_overlapping_in_list(start_line, start_char, end_line, end_char, entities_in_file):
                messagebox.showwarning("Overlap Detected", "The selected text overlaps with an existing entity.", parent=self.root)
                return

            file_data = self.annotations.setdefault(self.current_file_path, {"entities": [], "relations": []})
            entities_list = file_data.setdefault("entities", [])

            entity_id = uuid.uuid4().hex
            # Manual annotations do NOT get the 'propagated' flag (or it's False)
            annotation = {
                'id': entity_id,
                'start_line': start_line, 'start_char': start_char, # Use adjusted positions
                'end_line': end_line, 'end_char': end_char,         # Use adjusted positions
                'text': final_text,                                 # Use adjusted text
                'tag': tag
                # No 'propagated': True here for manual annotation
            }
            entities_list.append(annotation)

            # Apply visual tag (will be handled by apply_annotations_to_text)
            self.apply_annotations_to_text() # Re-apply all to handle this new one correctly

            # Update list display
            self.update_entities_list()

            # Select new entity in list (requires finding the tree row iid using adjusted positions)
            self.root.update_idletasks()
            try:
                # Find the tree row iid corresponding to the new entity
                new_tree_row_iid = None
                if entity_id in self._entity_id_to_tree_iids:
                    # Find the specific row iid based on position if multiple exist (shouldn't for new)
                    pos_str = f"{start_line}.{start_char}" # Use adjusted start pos
                    for tree_iid in self._entity_id_to_tree_iids[entity_id]:
                        item_values = self.entities_tree.item(tree_iid, 'values')
                        if item_values and item_values[1] == pos_str: # Check start pos
                            new_tree_row_iid = tree_iid
                            break

                if new_tree_row_iid and self.entities_tree.exists(new_tree_row_iid):
                    self.entities_tree.selection_set(new_tree_row_iid)
                    self.entities_tree.focus(new_tree_row_iid)
                    self.entities_tree.see(new_tree_row_iid)
                    self.on_entity_select(None) # Trigger highlight update
                else:
                    print(f"Warning: Could not find treeview row for new entity {entity_id}")

            except Exception as e: print(f"Error selecting new entity in list: {e}")


            status_text = f"Annotated: '{final_text[:30].replace(os.linesep, ' ')}...' as {tag}"
            self.status_var.set(status_text)
            self._update_button_states() # Update buttons after successful annotation

        except tk.TclError as e:
            if "text doesn't contain selection" in str(e).lower():
                messagebox.showinfo("Info", "Please select text to annotate.", parent=self.root)
            else: messagebox.showerror("Annotation Error", f"A Tkinter error occurred:\n{e}", parent=self.root)
        except Exception as e: messagebox.showerror("Annotation Error", f"An unexpected error occurred:\n{e}", parent=self.root)

    # --- Entity Removal / Merging / Demerging (Keep these as they were) ---
    def remove_entity_annotation(self):
        """Removes selected entities (rows in treeview) and their associated relations."""
        selected_tree_iids = self.entities_tree.selection() # These are tree row iids
        if not selected_tree_iids:
            messagebox.showinfo("Info", "Select one or more entities from the list to remove.", parent=self.root)
            return
        if not self.current_file_path or self.current_file_path not in self.annotations:
            messagebox.showerror("Error", "Cannot remove entity: No file/annotations.", parent=self.root)
            return

        # Get the actual entity dictionaries corresponding to selected tree rows
        entities_to_remove_data = []
        entity_ids_to_remove = set() # Track the actual data IDs being removed
        entities_in_file = self.annotations.get(self.current_file_path, {}).get("entities", [])

        for tree_iid in selected_tree_iids:
             if not self.entities_tree.exists(tree_iid): continue
             try:
                 values = self.entities_tree.item(tree_iid, 'values')
                 entity_id = values[0] # Actual entity ID from hidden column
                 start_pos_str = values[1]
                 end_pos_str = values[2]
                 # Find the corresponding dict in the data
                 for entity_dict in entities_in_file:
                     if (entity_dict.get('id') == entity_id and
                         f"{entity_dict.get('start_line')}.{entity_dict.get('start_char')}" == start_pos_str and
                         f"{entity_dict.get('end_line')}.{entity_dict.get('end_char')}" == end_pos_str):
                         entities_to_remove_data.append(entity_dict)
                         entity_ids_to_remove.add(entity_id) # Add the actual data ID
                         break # Move to next selected tree iid
             except Exception as e:
                 print(f"Warning: Error getting data for selected tree item {tree_iid}: {e}")

        if not entities_to_remove_data:
             messagebox.showerror("Error", "Could not retrieve data for selected entities.", parent=self.root)
             return

        confirm = messagebox.askyesno("Confirm Removal",
            f"Remove {len(entities_to_remove_data)} selected entity instance(s)?\n"
            f"(Actual unique entity IDs affected: {len(entity_ids_to_remove)})\n"
            f"WARNING: This also removes relations associated with these *specific entity IDs*.", parent=self.root)
        if not confirm: return

        # Remove the specific dictionaries found
        original_count = len(entities_in_file)
        self.annotations[self.current_file_path]["entities"] = [
            e for e in entities_in_file if e not in entities_to_remove_data
        ]
        removed_entity_count = original_count - len(self.annotations[self.current_file_path]["entities"])

        # Remove associated relations (based on the actual entity IDs removed)
        relations = self.annotations[self.current_file_path].get("relations", [])
        relations_remaining = []
        removed_relation_count = 0
        if relations:
            relations_original_count = len(relations)
            relations_remaining = [
                rel for rel in relations
                if rel.get('head_id') not in entity_ids_to_remove and rel.get('tail_id') not in entity_ids_to_remove
            ]
            removed_relation_count = relations_original_count - len(relations_remaining)
            self.annotations[self.current_file_path]["relations"] = relations_remaining

        # Refresh UI
        self.update_entities_list() # This clears selection, which is okay after removal
        self.update_relations_list()
        self.apply_annotations_to_text() # Re-apply remaining highlights

        self.status_var.set(f"Removed {removed_entity_count} entity instances, {removed_relation_count} relations.")
        self._update_button_states() # Update buttons as selection is now empty

    def merge_selected_entities(self):
        """Merges selected entity instances (rows) in the list to share the same actual ID."""
        selected_tree_iids = self.entities_tree.selection() # Tree row iids
        if len(selected_tree_iids) < 2:
            messagebox.showinfo("Info", "Select 2+ entity instances from the list to merge.", parent=self.root)
            return
        if not self.current_file_path or self.current_file_path not in self.annotations:
            messagebox.showerror("Error", "Cannot merge: No file/annotations.", parent=self.root)
            return

        # Get the actual entity dictionaries for the selected rows
        selected_entities_data = []
        entities_in_file = self.annotations.get(self.current_file_path, {}).get("entities", [])
        processed_positions = set() # Ensure we don't process the exact same instance twice if selected weirdly

        for tree_iid in selected_tree_iids:
             if not self.entities_tree.exists(tree_iid): continue
             try:
                 values = self.entities_tree.item(tree_iid, 'values')
                 entity_id = values[0]
                 start_pos_str = values[1]
                 end_pos_str = values[2]
                 pos_key = (start_pos_str, end_pos_str)

                 if pos_key in processed_positions: continue # Already got this one

                 # Find the corresponding dict
                 for entity_dict in entities_in_file:
                     if (entity_dict.get('id') == entity_id and
                         f"{entity_dict.get('start_line')}.{entity_dict.get('start_char')}" == start_pos_str and
                         f"{entity_dict.get('end_line')}.{entity_dict.get('end_char')}" == end_pos_str):
                         # Check if essential keys exist before adding
                         if all(k in entity_dict for k in ['id', 'start_line', 'start_char', 'end_line', 'end_char']):
                             selected_entities_data.append(entity_dict)
                             processed_positions.add(pos_key)
                         else:
                             print(f"Warning: Skipping entity at {start_pos_str} in merge - missing position data.")
                         break
             except Exception as e:
                 print(f"Warning: Error getting data for selected tree item {tree_iid} during merge: {e}")

        if len(selected_entities_data) < 2:
            messagebox.showerror("Error", "Need at least two valid entity instances with position data to merge.", parent=self.root)
            return

        # Determine the canonical ID (from the entity that appears earliest in the text)
        selected_entities_data.sort(key=lambda e: (e.get('start_line', 0), e.get('start_char', 0)))
        canonical_entity_dict = selected_entities_data[0]
        canonical_id = canonical_entity_dict.get('id')

        if not canonical_id:
             messagebox.showerror("Error", "Failed to determine canonical ID for merge.", parent=self.root)
             return

        ids_to_change = {e.get('id') for e in selected_entities_data if e.get('id') != canonical_id}
        dicts_to_change = [e for e in selected_entities_data if e.get('id') != canonical_id]

        if not dicts_to_change:
            messagebox.showinfo("Info", "Selected entity instances already share the same ID.", parent=self.root)
            return

        confirm = messagebox.askyesno("Confirm Merge",
             f"Merge {len(selected_entities_data)} selected instances?\n"
             f"All will share the ID of the earliest instance ('{canonical_entity_dict.get('text', '')[:20]}...').\n"
             f"Relations involving changed IDs will be updated. Duplicate relations removed.", parent=self.root)
        if not confirm:
            self.status_var.set("Merge cancelled.")
            return

        modified_entity_count = 0
        modified_relation_count = 0

        # 1. Update Entity IDs *for the specific instances selected*
        #    Does NOT change the 'propagated' status of the instances.
        for entity_dict in dicts_to_change:
            # Find the dict in the main list and update it
            for i, main_list_dict in enumerate(entities_in_file):
                 # Use position to ensure we change the right instance
                 if (main_list_dict.get('start_line') == entity_dict.get('start_line') and
                     main_list_dict.get('start_char') == entity_dict.get('start_char') and
                     main_list_dict.get('end_line') == entity_dict.get('end_line') and
                     main_list_dict.get('end_char') == entity_dict.get('end_char') and
                     main_list_dict.get('id') == entity_dict.get('id')): # Check original ID too
                     entities_in_file[i]['id'] = canonical_id
                     modified_entity_count += 1
                     break # Found and modified this instance

        # 2. Update Relation IDs
        # Any relation pointing to an ID that was changed *away from* needs to point to the canonical ID
        relations = self.annotations[self.current_file_path].get("relations", [])
        if relations and ids_to_change: # Only if relations exist and IDs were actually changed
            for i, rel in enumerate(relations):
                relation_modified = False
                if rel.get('head_id') in ids_to_change:
                    relations[i]['head_id'] = canonical_id
                    relation_modified = True
                if rel.get('tail_id') in ids_to_change:
                    relations[i]['tail_id'] = canonical_id
                    relation_modified = True
                if relation_modified: modified_relation_count += 1

        # 3. Remove duplicate relations potentially created by merge
        removed_duplicates = 0
        if relations and modified_relation_count > 0: # Only check if changes might have occurred
            unique_relations = []
            seen_signatures = set() # (head_id, tail_id, type)
            for rel in relations:
                sig = (rel.get('head_id'), rel.get('tail_id'), rel.get('type'))
                if sig not in seen_signatures:
                    seen_signatures.add(sig)
                    unique_relations.append(rel)
                else:
                    removed_duplicates += 1

            if removed_duplicates > 0:
                self.annotations[self.current_file_path]["relations"] = unique_relations

        # --- Update UI ---
        self.update_entities_list() # Will re-render with 'merged' tag and updated IDs
        self.update_relations_list() # Will show updated head/tail
        self.apply_annotations_to_text() # Re-apply highlights (incl. underlines based on original status)

        # Re-select the items that were part of the merge (now share the canonical ID)
        self.root.update_idletasks()
        tree_iids_to_reselect = []
        try:
            # Find all tree rows whose underlying data now has the canonical ID
            if canonical_id in self._entity_id_to_tree_iids:
                tree_iids_to_reselect = self._entity_id_to_tree_iids[canonical_id]

            if tree_iids_to_reselect:
                self.entities_tree.selection_set(tree_iids_to_reselect)
                self.entities_tree.focus(tree_iids_to_reselect[0]) # Focus first one
                self.entities_tree.see(tree_iids_to_reselect[0])
                self.on_entity_select(None) # Update highlights etc.
            else:
                self.selected_entity_ids_for_relation = [] # Clear if selection failed
                self._update_button_states()

        except Exception as e:
            print(f"Warning: Error re-selecting merged entities: {e}")
            self.selected_entity_ids_for_relation = []
            self._update_button_states()


        # Update status
        status_msg = f"Merged {len(selected_entities_data)} instances to ID {canonical_id[:6]}.... Updated {modified_relation_count} relations."
        if removed_duplicates > 0: status_msg += f" Removed {removed_duplicates} duplicates."
        self.status_var.set(status_msg)
        # Button states are updated by on_entity_select or the error handler

    def _on_text_right_click(self, event):
        """Handles right-clicks on the text area to show context menu."""
        if not self.current_file_path or self.text_area.cget('state') == tk.DISABLED:
            return # Only works when a file is loaded and text area is active

        # Find the text index (line.char) at the click position
        try:
            click_index_str = self.text_area.index(f"@{event.x},{event.y}")
            click_line, click_char = map(int, click_index_str.split('.'))
        except tk.TclError:
            return # Clicked outside text content

        # Find which entity annotation (if any) contains the click position
        clicked_entity_dict = None
        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        # Iterate in reverse order so topmost annotation is found first if overlapping
        for entity in reversed(entities):
            start_l, start_c = entity.get('start_line'), entity.get('start_char')
            end_l, end_c = entity.get('end_line'), entity.get('end_char')

            if start_l is None or start_c is None or end_l is None or end_c is None:
                continue # Skip entities with missing position data

            # Check if click is within the span (inclusive start, exclusive end logic for Tk Text)
            span_start = (start_l, start_c)
            span_end = (end_l, end_c)
            click_pos = (click_line, click_char)

            # Check if click is within the span defined by (start_l, start_c) and (end_l, end_c)
            if span_start <= click_pos < span_end:
                 clicked_entity_dict = entity
                 break # Found the entity under the cursor

        if not clicked_entity_dict:
            return # Click wasn't on a known annotation span

        # Check if the found entity is part of a merge group
        entity_id = clicked_entity_dict.get('id')
        is_merged = False
        if entity_id:
            count = sum(1 for e in entities if e.get('id') == entity_id)
            if count > 1:
                is_merged = True

        # --- Create and show context menu ---
        context_menu = tk.Menu(self.root, tearoff=0)

        if is_merged:
            context_menu.add_command(
                label="Demerge This Instance",
                command=lambda e=clicked_entity_dict: self.demerge_entity(e) # Pass specific dict
            )
            context_menu.add_separator()
            status = "Merged"
        else:
            context_menu.add_command(label="Demerge This Instance", state=tk.DISABLED)
            context_menu.add_separator()
            status = "Not Merged"

        # Add other useful info/actions
        context_menu.add_command(
            label=f"ID: {entity_id[:8]}... ({status})",
            state=tk.DISABLED
        )
        context_menu.add_command(
             label=f"Tag: {clicked_entity_dict.get('tag', 'N/A')}",
             state=tk.DISABLED
        )
        # Add info about propagation status
        propagated_status = "Propagated" if clicked_entity_dict.get('propagated', False) else "Manual"
        context_menu.add_command(
             label=f"Origin: {propagated_status}",
             state=tk.DISABLED
        )


        try:
            context_menu.tk_popup(event.x_root, event.y_root)
        finally:
            context_menu.grab_release() # Ensure menu doesn't block interaction

    def demerge_entity(self, entity_dict_to_demerge):
        """
        Assigns a new unique ID to a specific entity instance that was previously merged.
        Does NOT change the 'propagated' status.
        """
        if not self.current_file_path: return

        file_data = self.annotations.get(self.current_file_path)
        if not file_data or "entities" not in file_data: return

        entities_list = file_data["entities"]

        # Find the exact dictionary object in our list
        found_index = -1
        for i, entity in enumerate(entities_list):
            # Use position and original ID to identify the exact dictionary instance
            if (entity.get('id') == entity_dict_to_demerge.get('id') and
                entity.get('start_line') == entity_dict_to_demerge.get('start_line') and
                entity.get('start_char') == entity_dict_to_demerge.get('start_char') and
                entity.get('end_line') == entity_dict_to_demerge.get('end_line') and
                entity.get('end_char') == entity_dict_to_demerge.get('end_char')):
                found_index = i
                break

        if found_index == -1:
            messagebox.showerror("Error", "Could not find the specific entity instance to demerge in the data list.", parent=self.root)
            return

        original_id = entities_list[found_index].get('id')
        new_id = uuid.uuid4().hex

        # --- Perform the demerge ---
        entities_list[found_index]['id'] = new_id

        # --- Update UI ---
        self.update_entities_list()
        self.apply_annotations_to_text()
        self.update_relations_list()

        # 4. Update status
        demerged_text = entities_list[found_index].get('text', '').replace('\n', ' ')[:30]
        self.status_var.set(f"Demerged instance '{demerged_text}...'. New ID assigned.")

        # 5. Update button states
        self._update_button_states()

        # Optional: Try to select the newly demerged entity in the list
        try:
            self.root.update_idletasks()
            new_tree_row_iid = None
            for tree_iid in self.entities_tree.get_children(""):
                row_values = self.entities_tree.item(tree_iid, 'values')
                if row_values and row_values[0] == new_id: # Check the actual entity ID
                    # Check position match too, just in case
                    if (f"{entity_dict_to_demerge['start_line']}.{entity_dict_to_demerge['start_char']}" == row_values[1] and
                        f"{entity_dict_to_demerge['end_line']}.{entity_dict_to_demerge['end_char']}" == row_values[2]):
                        new_tree_row_iid = tree_iid
                        break

            if new_tree_row_iid and self.entities_tree.exists(new_tree_row_iid):
                self.entities_tree.selection_set(new_tree_row_iid)
                self.entities_tree.focus(new_tree_row_iid)
                self.entities_tree.see(new_tree_row_iid)
                self.on_entity_select(None) # Trigger updates
            else:
                print("Warning: Could not find or select the demerged entity row in the list.")
        except Exception as e:
            print(f"Warning: Could not select demerged entity in list: {e}")


    # --- Entity Highlighting and List Updates ---
    def apply_annotations_to_text(self):
        """Applies highlighting (bg color and underline) for entities of the current file."""
        if not self.current_file_path or self.text_area.cget('state') == tk.DISABLED:
            return # Don't try if no file or text area is disabled

        original_state = self.text_area.cget('state')
        if original_state == tk.DISABLED: self.text_area.config(state=tk.NORMAL)

        # --- Clear existing tags first ---
        current_text_tags = list(self.text_area.tag_names())
        tags_to_remove = set(self.entity_tags)
        tags_to_remove.add("propagated_entity") # Make sure to remove the underline tag too
        for tag_name in current_text_tags:
            if tag_name in tags_to_remove and tag_name != tk.SEL: # Don't remove selection tag
                try:
                    self.text_area.tag_remove(tag_name, "1.0", tk.END)
                except tk.TclError: pass # Ignore if tag doesn't exist
        # --- End Clearing ---

        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        # Sort by position to handle potential overlaps predictably (though overlaps shouldn't exist)
        sorted_entities = sorted(entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0)))

        # Re-apply tags
        for ann in sorted_entities:
            try:
                start_pos = f"{ann['start_line']}.{ann['start_char']}"
                end_pos = f"{ann['end_line']}.{ann['end_char']}"
                tag = ann.get('tag')
                is_propagated = ann.get('propagated', False) # Check if propagated

                if tag and tag in self.entity_tags:
                    # Ensure background tag is configured (might be newly loaded/added)
                    if tag not in self.text_area.tag_names():
                        self._configure_text_tags() # Define if missing

                    # Apply background tag if configured
                    if tag in self.text_area.tag_names():
                        self.text_area.tag_add(tag, start_pos, end_pos)

                        # --- APPLY UNDERLINE TAG IF PROPAGATED ---
                        if is_propagated:
                            try:
                                # Ensure the underline tag exists
                                if "propagated_entity" not in self.text_area.tag_names():
                                     self.text_area.tag_configure("propagated_entity", underline=True)
                                # Apply the underline tag IN ADDITION to the background tag
                                self.text_area.tag_add("propagated_entity", start_pos, end_pos)
                            except tk.TclError as e:
                                print(f"Warning: Could not apply underline tag for propagated entity {ann.get('id', 'N/A')}: {e}")
                        # --- END UNDERLINE APPLICATION ---

                    else: print(f"Warning: Entity {ann.get('id','N/A')} tag '{tag}' unconfigurable.")
                elif tag: print(f"Warning: Entity {ann.get('id','N/A')} has unknown tag '{tag}'.")
            except KeyError as e: print(f"Warning: Entity {ann.get('id','N/A')} missing position key {e}. Cannot highlight.")
            except Exception as e: print(f"Warning: Error applying tag for entity {ann.get('id','N/A')}: {e}")

        self.text_area.config(state=original_state) # Restore original state


    def update_entities_list(self):
        """Updates the Entities Treeview with entities for the current file."""
        # Keep existing selection (using actual entity IDs + positions) to restore it later
        selected_data_keys = set()
        selected_tree_iids = self.entities_tree.selection()
        for tree_iid in selected_tree_iids:
            if not self.entities_tree.exists(tree_iid): continue
            try:
                vals = self.entities_tree.item(tree_iid, 'values')
                # Use (entity_id, start_pos, end_pos) as a key to identify the selected data item
                selected_data_keys.add( (vals[0], vals[1], vals[2]) )
            except Exception: pass


        try: self.entities_tree.delete(*self.entities_tree.get_children())
        except Exception: pass
        self._entity_id_to_tree_iids = {} # Reset mapping


        if not self.current_file_path: # Handle case where file loading failed or no file loaded
            self._update_button_states()
            return

        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        if not entities:
            self.selected_entity_ids_for_relation = [] # Ensure clear if list empty
            self._update_button_states()
            return

        # Use a stable sort key for consistency when restoring selection
        sorted_entities = sorted(entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0), a.get('id', '')))

        # Count ID occurrences for 'merged' tag
        entity_id_counts = {}
        for ann in sorted_entities:
            entity_id = ann.get('id')
            if entity_id: entity_id_counts[entity_id] = entity_id_counts.get(entity_id, 0) + 1

        # Store mapping from actual entity ID to the list of treeview row iids using it
        tree_iids_to_restore = []

        # Populate tree
        for ann_index, ann in enumerate(sorted_entities): # Use enumerate for a unique index
            entity_id = ann.get('id')
            if not entity_id: continue # Skip invalid data

            try:
                start_line, start_char = ann['start_line'], ann['start_char']
                end_line, end_char = ann['end_line'], ann['end_char']
                start_pos_str = f"{start_line}.{start_char}"
                end_pos_str = f"{end_line}.{end_char}"

                full_text = ann.get('text', '') # Should be stripped already if propagated
                display_text = full_text.replace(os.linesep, ' ').replace('\n', ' ').replace('\r', '')[:60]
                if len(full_text) > 60: display_text += "..."
                tag = ann.get('tag', 'N/A')

                # Apply 'merged' tag if needed (based on count of the *actual* entity ID)
                treeview_tags = ('merged',) if entity_id_counts.get(entity_id, 0) > 1 else ()

                # Use a unique identifier for the treeview row iid
                tree_row_iid = f"entity_{start_pos_str}_{end_pos_str}"
                tree_row_iid += f"_{ann_index}"

                # Store the actual entity ID in the hidden 'ID' column (index 0 of values)
                values_to_insert = (entity_id, start_pos_str, end_pos_str, display_text, tag)

                self.entities_tree.insert("", tk.END, iid=tree_row_iid, # Use unique row id
                                          values=values_to_insert,
                                          tags=treeview_tags
                                         )

                # Map the actual entity ID to this tree row iid
                if entity_id not in self._entity_id_to_tree_iids:
                    self._entity_id_to_tree_iids[entity_id] = []
                self._entity_id_to_tree_iids[entity_id].append(tree_row_iid)

                # Check if this row corresponds to a previously selected data item
                data_key = (entity_id, start_pos_str, end_pos_str)
                if data_key in selected_data_keys:
                    tree_iids_to_restore.append(tree_row_iid)

            except KeyError as e: print(f"Error adding entity {entity_id} to list: Missing key {e}")
            except Exception as e: print(f"Error adding entity {entity_id} to list: {e}")

        # Restore selection if possible
        if tree_iids_to_restore:
            try:
                self.entities_tree.selection_set(tree_iids_to_restore)
                self.entities_tree.focus(tree_iids_to_restore[0])
                self.entities_tree.see(tree_iids_to_restore[0])
                # Update internal state based on restored selection
                self.on_entity_select(None)
            except Exception as e:
                print(f"Warning: Could not fully restore selection after update: {e}")
                self.selected_entity_ids_for_relation = [] # Clear if restoration failed
        else:
             self.selected_entity_ids_for_relation = [] # Clear selection state if nothing restored


        self._update_button_states() # Update buttons based on final selection


    def on_entity_select(self, event):
        """Handles selection changes in the Entities Treeview."""
        selected_tree_iids = self.entities_tree.selection() # Tree row iids

        # Update internal list of *actual* entity IDs selected for relation creation
        self.selected_entity_ids_for_relation = []
        entity_ids_in_selection = set()
        for tree_iid in selected_tree_iids:
            if not self.entities_tree.exists(tree_iid): continue
            try:
                values = self.entities_tree.item(tree_iid, 'values')
                actual_entity_id = values[0] # Get ID from hidden column
                if actual_entity_id:
                    # Store unique actual IDs. Order matters for head/tail, so use list.
                    # If an ID is already there (multiple instances selected), don't add again.
                    if actual_entity_id not in entity_ids_in_selection:
                        self.selected_entity_ids_for_relation.append(actual_entity_id)
                        entity_ids_in_selection.add(actual_entity_id)
            except Exception as e:
                print(f"Warning: Could not get entity ID from selected tree row {tree_iid}: {e}")

        # Highlight corresponding text spans
        if self.text_area.cget('state') == tk.NORMAL:
            self.text_area.tag_remove(tk.SEL, "1.0", tk.END) # Remove previous selection
            first_entity_pos = None

            for tree_iid in selected_tree_iids:
                 if not self.entities_tree.exists(tree_iid): continue
                 try:
                     values = self.entities_tree.item(tree_iid, 'values')
                     # Don't need the data dict here, just the positions from the tree row
                     start_pos_str = values[1]
                     end_pos_str = values[2]
                     try:
                         self.text_area.tag_add(tk.SEL, start_pos_str, end_pos_str)
                         if first_entity_pos is None: first_entity_pos = start_pos_str
                     except tk.TclError as te: print(f"Warning: Error highlighting entity: {te}")
                 except Exception as e:
                     print(f"Warning: Error processing selection highlight for row {tree_iid}: {e}")


            # Scroll to first selected entity
            if first_entity_pos:
                try: self.text_area.see(first_entity_pos)
                except tk.TclError as e: print(f"Warning: Error scrolling to entity: {e}")

        self._update_button_states() # Update buttons based on selection


    # --- Relation Annotation (Keep methods add_relation, flip_selected_relation, remove_relation_annotation, update_relations_list, on_relation_select as they were) ---
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

        # Check for duplicates (Head ID, Tail ID, Type must all match)
        if any(r.get('head_id') == head_id and r.get('tail_id') == tail_id and r.get('type') == relation_type for r in relations_list):
            messagebox.showwarning("Duplicate Relation", "This exact relation (same Head ID, Tail ID, and Type) already exists.", parent=self.root)
            return

        relation_id = uuid.uuid4().hex
        new_relation = {"id": relation_id, "type": relation_type, "head_id": head_id, "tail_id": tail_id}
        relations_list.append(new_relation)
        self.update_relations_list()

        # Select new relation in the list
        self.root.update_idletasks()
        try:
            if self.relations_tree.exists(relation_id): # Relation ID is used as iid here
                self.relations_tree.selection_set(relation_id)
                self.relations_tree.focus(relation_id)
                self.relations_tree.see(relation_id)
                self.on_relation_select(None) # Update buttons
            else: print(f"Warning: Could not find new relation {relation_id} in tree.")
        except Exception as e: print(f"Error selecting new relation: {e}")

        self.status_var.set(f"Added Relation: {relation_type} ({head_id[:4]}... -> {tail_id[:4]}...)")

    def flip_selected_relation(self):
        """Flips the Head and Tail entity IDs for the selected relation."""
        selected_iids = self.relations_tree.selection() # Relation ID is the iid here
        if len(selected_iids) != 1: return # Should be disabled if not 1

        relation_id_to_flip = selected_iids[0]
        relations = self.annotations.get(self.current_file_path, {}).get("relations")
        if not relations: return # No relations to flip

        found = False
        for i, rel in enumerate(relations):
            if rel.get('id') == relation_id_to_flip:
                current_head, current_tail = rel.get('head_id'), rel.get('tail_id')
                if current_head and current_tail:
                    # Check if flipping would create a duplicate
                    if any(r.get('head_id') == current_tail and r.get('tail_id') == current_head and r.get('type') == rel.get('type') for r in relations if r.get('id') != relation_id_to_flip):
                        messagebox.showwarning("Duplicate Relation", "Flipping this relation would create a duplicate of an existing relation.", parent=self.root)
                        return # Don't flip if it creates exact duplicate

                    relations[i]['head_id'], relations[i]['tail_id'] = current_tail, current_head # Swap
                    found = True
                    break
                else:
                    messagebox.showerror("Data Error", "Selected relation missing Head/Tail ID.", parent=self.root)
                    return

        if found:
            self.update_relations_list()
            # Re-select
            self.root.update_idletasks()
            try:
                if self.relations_tree.exists(relation_id_to_flip):
                    self.relations_tree.selection_set(relation_id_to_flip)
                    self.relations_tree.focus(relation_id_to_flip)
                    self.relations_tree.see(relation_id_to_flip)
                    self.on_relation_select(None) # Update buttons
            except Exception as e: print(f"Warning: Error re-selecting flipped relation: {e}")
            self.status_var.set("Relation Head/Tail flipped.")


    def remove_relation_annotation(self):
        """Removes the selected relation from the Relations list."""
        selected_iids = self.relations_tree.selection() # Relation ID is iid
        if len(selected_iids) != 1: return # Should be disabled if not 1

        relation_id_to_remove = selected_iids[0]
        relations = self.annotations.get(self.current_file_path, {}).get("relations")
        if not relations: return # No relations to remove

        original_length = len(relations)
        self.annotations[self.current_file_path]["relations"] = [
            rel for rel in relations if rel.get('id') != relation_id_to_remove
        ]

        if len(self.annotations[self.current_file_path]["relations"]) < original_length:
            self.update_relations_list() # Clears selection
            self.status_var.set("Relation removed.")
            self._update_button_states() # Update based on cleared selection
        else:
            messagebox.showwarning("Not Found", "Could not find the selected relation to remove.", parent=self.root)


    def update_relations_list(self):
        """Updates the Relations Treeview with relations for the current file."""
        selected_rel_iids = self.relations_tree.selection()

        try: self.relations_tree.delete(*self.relations_tree.get_children())
        except Exception: pass

        if not self.current_file_path: # Handle case where file loading failed or no file loaded
            self._update_button_states()
            return

        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        relations = self.annotations.get(self.current_file_path, {}).get("relations", [])

        if not relations:
            self._update_button_states() # Update buttons even if list is empty now
            return

        # Build lookup map from ALL entities in this file
        entity_display_map = {}
        processed_ids_for_map = set()
        sorted_entities_for_map = sorted(entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0)))
        for entity in sorted_entities_for_map:
             eid = entity.get('id')
             if eid and eid not in processed_ids_for_map:
                 etext = entity.get('text', 'N/A') # Should be stripped
                 display_text = etext.replace(os.linesep, ' ').replace('\n',' ').replace('\r','')[:30]
                 if len(etext) > 30: display_text += "..."
                 entity_display_map[eid] = display_text
                 processed_ids_for_map.add(eid)


        sorted_relations = sorted(relations, key=lambda r: (r.get('type', ''), r.get('head_id','')))

        for rel in sorted_relations:
            rel_id, head_id, tail_id, rel_type = rel.get('id'), rel.get('head_id'), rel.get('tail_id'), rel.get('type')
            if not (rel_id and head_id and tail_id and rel_type): continue # Skip invalid

            head_text = entity_display_map.get(head_id, f"<ID: {head_id[:6]}...>")
            tail_text = entity_display_map.get(tail_id, f"<ID: {tail_id[:6]}...>")
            values_to_insert = (rel_id, head_text, rel_type, tail_text)

            try:
                self.relations_tree.insert("", tk.END, iid=rel_id, values=values_to_insert)
            except Exception as e: print(f"Error inserting relation {rel_id} into tree: {e}")

        # Restore selection
        valid_selection = [rid for rid in selected_rel_iids if self.relations_tree.exists(rid)]
        if valid_selection:
            try:
                self.relations_tree.selection_set(valid_selection)
                self.relations_tree.focus(valid_selection[0])
                self.relations_tree.see(valid_selection[0])
            except Exception as e: print(f"Warning: Could not restore relation selection: {e}")

        self._update_button_states() # Update buttons after list refresh


    def on_relation_select(self, event):
        """Handles selection changes in the Relations Treeview."""
        self._update_button_states()


    # --- Propagation ---
    def propagate_annotations(self):
        """Propagate ENTITY annotations based on text/tag pairs from the *current* file to ALL files."""
        if not self.current_file_path or not self.files_list:
            messagebox.showinfo("Info", "Load a directory first.", parent=self.root)
            return
        source_entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        if not source_entities:
            messagebox.showinfo("Info", "No entities in current file to propagate.", parent=self.root)
            return

        text_to_tag = {}
        processed_texts = set()
        sorted_source = sorted(source_entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0)))
        for ann in sorted_source:
             text = ann.get('text','').strip() # Use stripped text from source
             tag = ann.get('tag')
             if text and tag and text not in processed_texts:
                 text_to_tag[text] = tag
                 processed_texts.add(text)

        if not text_to_tag:
            messagebox.showinfo("Info", "No valid text/tag pairs found in current file to propagate.", parent=self.root)
            return

        confirm = messagebox.askyesno("Confirm Propagation (Current File)",
             f"Search for {len(text_to_tag)} unique text/tag pairs from '{os.path.basename(self.current_file_path)}' "
             f"across all {len(self.files_list)} files?\n\n"
             f"WARNING: Adds new entities (underlined, whitespace stripped). Skips overlaps. Relations not propagated.", parent=self.root)
        if not confirm:
            self.status_var.set("Propagation cancelled.")
            return
        self._perform_propagation(text_to_tag, "Current File Propagation")

    def load_and_propagate_from_dictionary(self):
        """Loads a dictionary file and propagates entities based on it."""
        if not self.files_list:
            messagebox.showerror("Error", "Open a directory first.", parent=self.root)
            return
        if not self.entity_tags:
            messagebox.showwarning("Warning", "No entity tags defined in Settings.", parent=self.root)
            return

        dict_path = filedialog.askopenfilename(
            title="Select Dictionary File (Text<TAB/SPACE>Tag per line)",
            filetypes=[("Text files", "*.txt"), ("TSV files", "*.tsv"), ("All files", "*.*")],
            parent=self.root
        )
        if not dict_path: return

        dictionary_mapping = {}
        lines_read, skipped_lines = 0, 0
        invalid_tags_found = set()
        duplicate_texts = 0
        try:
            with open(dict_path, 'r', encoding='utf-8') as f:
                for line_num, line in enumerate(f, 1):
                    lines_read += 1
                    line = line.strip()
                    if not line or line.startswith('#'): skipped_lines +=1; continue

                    parts = line.split('\t')
                    if len(parts) != 2: parts = line.rsplit(maxsplit=1)
                    if len(parts) != 2:
                        print(f"Warning: Skipping malformed dict line {line_num}: '{line}'")
                        skipped_lines += 1; continue

                    entity_text, label = parts[0].strip(), parts[1].strip() # Strip text from dictionary
                    if not entity_text: skipped_lines += 1; continue

                    if label not in self.entity_tags:
                         invalid_tags_found.add(label)
                         skipped_lines += 1
                         continue

                    if entity_text in dictionary_mapping and dictionary_mapping[entity_text] != label:
                        duplicate_texts += 1
                    dictionary_mapping[entity_text] = label

        except Exception as e:
            messagebox.showerror("Dictionary Read Error", f"Failed to read dictionary:\n{e}", parent=self.root)
            return

        valid_entries = len(dictionary_mapping)
        # Note: skipped_lines count might be slightly off due to duplicates, but ok for info
        if not dictionary_mapping:
             msg = f"Finished reading dictionary '{os.path.basename(dict_path)}'.\n"
             msg += f"Read {lines_read} lines. Found 0 valid entries.\n"
             if invalid_tags_found: msg += f"Skipped lines due to unrecognized tags (e.g., {', '.join(list(invalid_tags_found)[:5])}...).\n"
             if skipped_lines > len(invalid_tags_found): msg += f"Other lines skipped (formatting/empty)."
             messagebox.showinfo("Dictionary Results", msg, parent=self.root)
             return

        confirm_msg = f"Dictionary '{os.path.basename(dict_path)}' loaded.\n"
        confirm_msg += f"- Found {valid_entries} unique entries with valid tags.\n"
        confirm_msg += f"- Read {lines_read} total lines ({skipped_lines} skipped, {duplicate_texts} duplicates overwritten).\n"
        if invalid_tags_found: confirm_msg += f"- Example skipped tags: {', '.join(list(invalid_tags_found)[:5])}{'...' if len(invalid_tags_found)>5 else ''}\n"
        confirm_msg += f"\nPropagate these {valid_entries} annotations across {len(self.files_list)} files?\n\n(Adds new entities (underlined, whitespace stripped). Skips overlaps. Relations not affected.)"

        confirm = messagebox.askyesno("Confirm Dictionary Propagation", confirm_msg, parent=self.root)
        if not confirm:
            self.status_var.set("Dictionary propagation cancelled.")
            return
        self._perform_propagation(dictionary_mapping, "Dictionary Propagation")


    def _perform_propagation(self, text_to_tag_map, source_description):
        """
        COMMON entity propagation logic. Adds 'propagated'=True flag,
        strips whitespace from found text, adjusts positions accordingly,
        and performs overlap checks based on adjusted positions.
        """
        propagated_count = 0
        affected_files_count = 0
        extend_option = self.extend_to_word.get()
        current_file_was_modified = False

        self.status_var.set(f"Starting {source_description}...")
        self.root.update_idletasks()

        # Sort texts to find by length (longest first) to avoid partial matches being annotated first
        sorted_texts_to_find = sorted(text_to_tag_map.keys(), key=len, reverse=True)

        for i, file_path in enumerate(self.files_list):
            file_modified_in_this_run = False
            # Update status periodically
            if (i + 1) % 10 == 0 or i == len(self.files_list) - 1:
                self.status_var.set(f"{source_description}: Processing file {i+1}/{len(self.files_list)}...")
                self.root.update_idletasks()

            # Skip processing if file was reported missing during session load or doesn't exist now
            if not os.path.isfile(file_path):
                print(f"Info: Skipping propagation for missing file: {file_path}")
                continue

            try:
                with open(file_path, 'r', encoding='utf-8') as f: content = f.read()
                # Use tk.Text methods to get accurate line/char positions matching the widget
                temp_text = tk.Text()
                temp_text.insert('1.0', content)

                file_data = self.annotations.setdefault(file_path, {"entities": [], "relations": []})
                target_entities_list = file_data.setdefault("entities", [])

                # Get existing annotations for this file for overlap checks
                # Make a copy of dicts to avoid modifying while iterating if needed later
                existing_entity_dicts = [e.copy() for e in target_entities_list]

                newly_added_this_file = [] # Track entities added *during this propagation run* for this file

                for text_to_find in sorted_texts_to_find:
                    tag_to_apply = text_to_tag_map[text_to_find]
                    if not text_to_find: continue # Skip empty search terms

                    start_index = "1.0"
                    while True:
                        # Find the raw match position using the search term
                        found_pos_str = temp_text.search(text_to_find, start_index, stopindex=tk.END, exact=True)
                        if not found_pos_str: break # Not found in the rest of the text

                        # Calculate initial end position based *only* on the length of the search term
                        initial_end_pos_str = temp_text.index(f"{found_pos_str}+{len(text_to_find)}c")

                        # --- Potentially Extend Span ---
                        current_match_start_pos = found_pos_str
                        current_match_end_pos = initial_end_pos_str
                        if extend_option:
                             try:
                                 word_start_pos = temp_text.search(r"\M", current_match_start_pos, backwards=True, regexp=True)
                                 if not word_start_pos: word_start_pos = temp_text.index(f"{current_match_start_pos} linestart")

                                 # Search from one char *before* initial end pos to find containing word end
                                 last_char_search_start = temp_text.index(f"{initial_end_pos_str}-1c")
                                 word_end_pos = temp_text.search(r"\m", f"{last_char_search_start}+1c", forwards=True, regexp=True)
                                 if not word_end_pos: word_end_pos = temp_text.index(f"{last_char_search_start} lineend")

                                 # Update positions only if extension actually changed them
                                 if word_start_pos != current_match_start_pos or word_end_pos != current_match_end_pos:
                                     current_match_start_pos = word_start_pos
                                     current_match_end_pos = word_end_pos
                             except tk.TclError as e:
                                 print(f"Warning: Regex word boundary search failed near {found_pos_str}: {e}. Using original match.")

                        # --- Get text of the current span and strip whitespace ---
                        span_text_with_potential_whitespace = temp_text.get(current_match_start_pos, current_match_end_pos)
                        stripped_text = span_text_with_potential_whitespace.strip()

                        # If stripping removed all content, skip this match
                        if not stripped_text:
                            start_index = current_match_end_pos # Advance past the empty match
                            continue

                        # --- Calculate Adjusted Positions for Stripped Text ---
                        leading_ws = len(span_text_with_potential_whitespace) - len(span_text_with_potential_whitespace.lstrip())
                        # trailing_ws = len(span_text_with_potential_whitespace) - len(span_text_with_potential_whitespace.rstrip()) # Not needed directly

                        adj_start_pos_str = temp_text.index(f"{current_match_start_pos}+{leading_ws}c")
                        # End position is start + length of stripped text
                        adj_end_pos_str = temp_text.index(f"{adj_start_pos_str}+{len(stripped_text)}c")

                        try:
                             adj_start_line, adj_start_char = map(int, adj_start_pos_str.split('.'))
                             adj_end_line, adj_end_char = map(int, adj_end_pos_str.split('.'))
                        except ValueError:
                             print(f"Error parsing adjusted positions: {adj_start_pos_str} / {adj_end_pos_str}")
                             start_index = current_match_end_pos # Advance past this problematic match
                             continue

                        # --- Perform Overlap Check using *Adjusted* Span ---
                        adjusted_span_tuple = (adj_start_line, adj_start_char, adj_end_line, adj_end_char)
                        overlap = False
                        # Check against pre-existing annotations in this file
                        if self._is_overlapping_in_list(*adjusted_span_tuple, existing_entity_dicts):
                            overlap = True
                        # Check against annotations added *during this propagation run* for this file
                        if not overlap and self._is_overlapping_in_list(*adjusted_span_tuple, newly_added_this_file):
                             overlap = True

                        # --- Add Annotation if No Overlap ---
                        if not overlap:
                            entity_id = uuid.uuid4().hex
                            new_annotation = {
                                'id': entity_id,
                                'start_line': adj_start_line, # Use adjusted position
                                'start_char': adj_start_char, # Use adjusted position
                                'end_line': adj_end_line,     # Use adjusted position
                                'end_char': adj_end_char,     # Use adjusted position
                                'text': stripped_text,        # Use stripped text
                                'tag': tag_to_apply,
                                'propagated': True           # Mark as propagated
                            }
                            target_entities_list.append(new_annotation) # Add to main list
                            newly_added_this_file.append(new_annotation) # Track for intra-file overlap checks

                            propagated_count += 1
                            file_modified_in_this_run = True
                            if file_path == self.current_file_path: current_file_was_modified = True

                        # Advance search position using the end of the *original match span* before stripping/extension
                        # to ensure we find subsequent occurrences correctly.
                        start_index = initial_end_pos_str

                temp_text.destroy() # Clean up temporary widget

            except Exception as e: print(f"ERROR processing file '{os.path.basename(file_path)}' during propagation:\n{str(e)}")

            if file_modified_in_this_run: affected_files_count += 1

        # Post-propagation updates
        if current_file_was_modified:
            # These will trigger apply_annotations_to_text which handles the underline
            self.update_entities_list()
            self.apply_annotations_to_text()
        self._update_button_states()

        summary = f"{source_description} complete.\nAdded {propagated_count} new entities (underlined) across {affected_files_count} files."
        if extend_option: summary += "\n('Extend to whole word' was enabled)"
        messagebox.showinfo("Propagation Results", summary, parent=self.root)
        self.status_var.set(f"{source_description} finished. Added {propagated_count} entities.")


    # --- Tag/Type Management (Keep methods _manage_items, manage_entity_tags, manage_relation_types as they were) ---
    def _manage_items(self, item_type_name, current_items_list, update_combobox_func):
        """Generic modal window for managing tags/types."""
        window = tk.Toplevel(self.root)
        window.title(f"Manage {item_type_name}")
        window.geometry("350x400"); window.minsize(300, 250) # Allow some resizing
        window.transient(self.root); window.grab_set()

        list_frame = tk.Frame(window); list_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(10, 0))
        tk.Label(list_frame, text=f"Current {item_type_name}:").pack(anchor=tk.W)
        scrollbar = tk.Scrollbar(list_frame); scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        listbox = tk.Listbox(list_frame, yscrollcommand=scrollbar.set, exportselection=False, selectmode=tk.EXTENDED)

        # Populate listbox with current items
        current_items_list.sort(key=str.lower) # Sort for consistent display
        for item in current_items_list:
            listbox.insert(tk.END, item)
            if item_type_name == "Entity Tags":
                color = self.get_color_for_tag(item)
                try: listbox.itemconfig(tk.END, {'bg': color})
                except tk.TclError: pass # Ignore color errors if listbox destroyed early

        listbox.pack(fill=tk.BOTH, expand=True)
        scrollbar.config(command=listbox.yview)

        controls_frame = tk.Frame(window); controls_frame.pack(fill=tk.X, padx=10, pady=5)
        item_var = tk.StringVar()
        item_entry = tk.Entry(controls_frame, textvariable=item_var, width=20)
        item_entry.grid(row=0, column=0, sticky="ew", padx=(0, 5))
        controls_frame.grid_columnconfigure(0, weight=1) # Make entry expand

        def add_item():
            item = item_var.get().strip()
            if item:
                existing_lower = [listbox.get(i).lower() for i in range(listbox.size())]
                if item.lower() not in existing_lower:
                    listbox.insert(tk.END, item)
                    # Keep list sorted
                    items = list(listbox.get(0, tk.END))
                    items.sort(key=str.lower)
                    listbox.delete(0, tk.END)
                    for sorted_item in items:
                        listbox.insert(tk.END, sorted_item)
                        if item_type_name == "Entity Tags":
                            color = self.get_color_for_tag(sorted_item) # Get/generate color
                            try: listbox.itemconfig(tk.END, {'bg': color})
                            except tk.TclError: pass

                    item_var.set(""); listbox.see(tk.END)
                else: messagebox.showwarning("Duplicate", f"'{item}' already exists (case-insensitive).", parent=window)
            item_entry.focus_set()
        item_entry.bind("<Return>", lambda event: add_item())

        add_btn = tk.Button(controls_frame, text="Add", width=7, command=add_item)
        add_btn.grid(row=0, column=1, padx=5)

        def remove_item():
            indices = listbox.curselection()
            if indices:
                items_to_remove = [listbox.get(i) for i in indices]
                if item_type_name == "Entity Tags":
                    # Check if tags are in use before confirming
                    tags_in_use = set()
                    for data in self.annotations.values():
                        for entity in data.get("entities", []):
                            if entity.get('tag') in items_to_remove:
                                tags_in_use.add(entity['tag'])
                    if tags_in_use:
                        if not messagebox.askyesno("Confirm Tag Removal",
                            f"You are removing tags that are currently used by annotations:\n"
                            f"- {', '.join(list(tags_in_use))}\n\n"
                            f"Annotations with these tags will remain but lose their highlighting and assigned tag.\n"
                            f"Continue?", parent=window):
                            return # User cancelled removal

                # Remove from listbox (iterate reversed indices)
                for index in sorted(indices, reverse=True): listbox.delete(index)
            else: messagebox.showwarning("No Selection", "Select item(s) to remove.", parent=window)

        remove_btn = tk.Button(controls_frame, text="Remove", width=7, command=remove_item)
        remove_btn.grid(row=0, column=2)

        button_frame = tk.Frame(window); button_frame.pack(fill=tk.X, padx=10, pady=(5, 10))

        def save_changes():
            new_items = list(listbox.get(0, tk.END))
            # Check if list actually changed (order doesn't matter here)
            if set(new_items) != set(current_items_list):
                removed_items = set(current_items_list) - set(new_items)
                added_items = set(new_items) - set(current_items_list)

                # Apply Changes
                current_items_list[:] = new_items # Update original list in place
                update_combobox_func() # Update the UI combobox

                if item_type_name == "Entity Tags":
                    # Ensure new tags have colors and config
                    for added_tag in added_items:
                        self.get_color_for_tag(added_tag) # Assign color if needed
                    self._configure_text_tags() # Configure all current tags (incl. new + propagated)

                    # Remove configurations for deleted tags only if they exist
                    for removed_tag in removed_items:
                        try: self.text_area.tag_delete(removed_tag)
                        except tk.TclError: pass # Ignore error if tag didn't exist
                        if removed_tag in self.tag_colors: del self.tag_colors[removed_tag] # Remove color mapping

                    # Re-apply highlights and update lists if tags changed
                    self.apply_annotations_to_text()
                    self.update_entities_list() # Tag column might change for remaining entities
                elif item_type_name == "Relation Types":
                     # If relation types are removed, update the relation list display
                     self.update_relations_list()

                self.status_var.set(f"{item_type_name} updated.")
            else:
                self.status_var.set(f"No changes made to {item_type_name}.")
            window.destroy()

        save_btn = tk.Button(button_frame, text="Save Changes", width=12, command=save_changes)
        save_btn.pack(side=tk.RIGHT, padx=5)
        cancel_btn = tk.Button(button_frame, text="Cancel", width=12, command=window.destroy)
        cancel_btn.pack(side=tk.RIGHT)

        item_entry.focus_set()
        window.wait_window()


    def manage_entity_tags(self):
        """Opens the modal window to manage entity tags."""
        self._manage_items("Entity Tags", self.entity_tags, self._update_entity_tag_combobox)

    def manage_relation_types(self):
        """Opens the modal window to manage relation types."""
        self._manage_items("Relation Types", self.relation_types, self._update_relation_type_combobox)


# --- Main Execution ---
def main():
    root = tk.Tk()
    # Optional: Apply a theme for a slightly more modern look if available
    try:
        style = ttk.Style()
        available_themes = style.theme_names()
        if 'clam' in available_themes: style.theme_use('clam')
        elif 'alt' in available_themes: style.theme_use('alt')
        elif 'vista' in available_themes: style.theme_use('vista') # Another common one
        elif 'xpnative' in available_themes: style.theme_use('xpnative')
        else: style.theme_use('default') # Fallback
    except tk.TclError:
        print("ttk themes not available or failed to set.") # Continue with default Tk look

    app = TextAnnotator(root)
    root.mainloop()

if __name__ == "__main__":
    main()
