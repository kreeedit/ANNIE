# -*- coding: utf-8 -*-
"""
ANNIE: Annotation Interface for Named-entity & Information Extraction.
Allows loading text files, annotating text spans (entities) with tags,
and annotating directed relations between entities.
Includes basic propagation for entities and management for tags/relation types.
Adds dictionary-based entity propagation, relation flipping, and entity merging.
Includes Save/Load Session functionality.
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
SESSION_FILE_VERSION = "1.3" # Anguelos recommendation and searching

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
        self.selected_entity_ids_for_relation = [] # Stores UUIDs from entities_tree

        # --- Sort Tracking --- (new section)
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
        self._configure_text_tags()
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
        # --- NEW: Session Save/Load ---
        file_menu.add_command(label="Load Session...", command=self.load_session)
        file_menu.add_command(label="Save Session", command=self.save_session)
        file_menu.add_command(label="Save Session As...", command=lambda: self.save_session(force_ask=True)) # Force save dialog
        file_menu.add_separator()
        # --- End New ---
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
            entities_tree_frame, columns=("ID", "Start", "End", "Text", "Tag"),
            displaycolumns=("Start", "End", "Text", "Tag"), show="headings",
            yscrollcommand=scrollbar_entities_y.set, selectmode='extended'
        )
        self.entities_tree.column("ID", width=0, stretch=False) # Hide ID column
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
            relations_tree_frame, columns=("ID", "Head", "Type", "Tail"),
            displaycolumns=("Head", "Type", "Tail"), show="headings",
            yscrollcommand=scrollbar_relations_y.set, selectmode='browse'
        )
        self.relations_tree.column("ID", width=0, stretch=False) # Hide ID column
        self.relations_tree.heading("Head", text="Head Entity", command=lambda: self._treeview_sort_column(self.relations_tree, "Head", False))
        self.relations_tree.heading("Type", text="Relation Type", command=lambda: self._treeview_sort_column(self.relations_tree, "Type", False))
        self.relations_tree.heading("Tail", text="Tail Entity", command=lambda: self._treeview_sort_column(self.relations_tree, "Tail", False))
        self.relations_tree.column("Head", width=250, anchor=tk.W, stretch=True)
        self.relations_tree.column("Type", width=120, anchor=tk.CENTER, stretch=False)
        self.relations_tree.column("Tail", width=250, anchor=tk.W, stretch=True)
        self.relations_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.relations_tree.bind("<<TreeviewSelect>>", self.on_relation_select)
        self.entities_tree.bind("<Key>", lambda event: self._treeview_key_navigate(self.entities_tree, event))
        scrollbar_relations_y.config(command=self.relations_tree.yview)

    # Sort function:
    def _treeview_sort_column(self, tree, col, reverse):
        """Sorts a Treeview by the specified column."""
        # Get the item IDs and their values in the given column
        data = [(tree.set(item, col), item) for item in tree.get_children("")]

        # Store current selection before sorting
        selection = tree.selection()

        # Perform the sort
        data.sort(reverse=reverse)

        # Move items in the tree according to sort order
        for index, (val, item) in enumerate(data):
            tree.move(item, "", index)

        # Restore selection
        if selection:
            tree.selection_set(selection)
            # Make first selected item visible
            tree.see(selection[0])

        # Update the header to show sort direction
        # First reset all headers to remove previous indicators
        tree_columns = tree["columns"]
        for column in tree_columns:
            if column != "ID":  # Skip the hidden ID column
                tree.heading(column, text=column.replace("▲", "").replace("▼", ""))

        # Update current sort column header
        display_col = col.replace("▲", "").replace("▼", "")  # Remove any existing indicators
        indicator = "▼" if reverse else "▲"
        tree.heading(col, text=f"{display_col} {indicator}",
                    command=lambda: self._treeview_sort_column(tree, col, not reverse))

    # Improved _treeview_key_navigate function:
    def _treeview_key_navigate(self, tree, event):
        """Handles keyboard navigation in a Treeview to jump to items starting with pressed letter."""
        # Get the character, ensure it's printable
        if not event.char or not event.char.isprintable() or len(event.char) != 1:
            return  # Let the event propagate for regular navigation keys

        char = event.char.lower()

        # Get all items
        all_items = tree.get_children("")
        if not all_items:
            return  # Empty tree

        # Get currently focused item index
        focused_item = tree.focus()
        current_idx = -1
        if focused_item:
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
            tree.selection_set(found_item)
            tree.focus(found_item)
            tree.see(found_item)
            # Trigger selection event programmatically
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
        """Configures background colors for all known entity tags in the text area."""
        for tag in self.entity_tags:
            color = self.get_color_for_tag(tag)
            try:
                self.text_area.tag_configure(tag, background=color)
            except tk.TclError as e:
                print(f"Warning: Could not configure text tag '{tag}': {e}")

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
        # Safe access to selected tag even if list is modified
        current_selection = self.selected_entity_tag.get()
        if not self.entity_tags:
            self.selected_entity_tag.set("")
            self.entity_tag_combobox.config(values=[], state=tk.DISABLED)
        else:
            self.entity_tag_combobox['values'] = self.entity_tags
            # If current selection is no longer valid or combobox was disabled, set to first
            if current_selection not in self.entity_tags or self.entity_tag_combobox['state'] == tk.DISABLED:
                self.selected_entity_tag.set(self.entity_tags[0])
            else:
                 # Ensure current selection remains if still valid
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
        num_entities_selected = len(self.entities_tree.selection())
        num_relations_selected = len(self.relations_tree.selection())

        # File Navigation
        self.prev_btn.config(state=tk.NORMAL if has_files and self.current_file_index > 0 else tk.DISABLED)
        self.next_btn.config(state=tk.NORMAL if has_files and self.current_file_index < len(self.files_list) - 1 else tk.DISABLED)

        # Text Area
        self.text_area.config(state=tk.NORMAL if file_loaded else tk.DISABLED)

        # Entity Buttons
        can_annotate_entity = file_loaded and self.entity_tags
        self.annotate_btn.config(state=tk.NORMAL if can_annotate_entity else tk.DISABLED)
        self.remove_entity_btn.config(state=tk.NORMAL if num_entities_selected > 0 else tk.DISABLED)
        self.merge_entities_btn.config(state=tk.NORMAL if num_entities_selected >= 2 else tk.DISABLED)
        can_propagate_current = file_loaded and self.annotations.get(self.current_file_path, {}).get("entities")
        self.propagate_btn.config(state=tk.NORMAL if can_propagate_current else tk.DISABLED)

        # Relation Buttons
        can_add_relation = num_entities_selected == 2 and self.relation_types
        self.add_relation_btn.config(state=tk.NORMAL if can_add_relation else tk.DISABLED)
        can_modify_relation = num_relations_selected == 1
        self.flip_relation_btn.config(state=tk.NORMAL if can_modify_relation else tk.DISABLED)
        self.remove_relation_btn.config(state=tk.NORMAL if can_modify_relation else tk.DISABLED)


    # --- File Handling ---
    def load_directory(self):
        """Opens a directory, lists .txt files, and loads the first one."""
        # --- Check for unsaved changes before discarding current state ---
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
                        # Basic check if it's actually a file (not a dir named .txt)
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

            self._update_button_states()

    def load_file(self, index):
        """Loads the content and annotations for the file at the given index."""
        if not (0 <= index < len(self.files_list)):
            print(f"Warning: Invalid file index {index} requested.")
            return

        # Check if index is actually changing
        if index == self.current_file_index and self.current_file_path:
            # No need to reload if it's the same file unless forced
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
            # Consider how to handle state: maybe clear current file info?
            # self.current_file_path = None
            # self.current_file_index = -1 # This might jump the user around undesirably
            self.status_var.set(f"Error loading {filename}")
            file_loaded_successfully = False

        # If loaded successfully, load/apply annotations
        if file_loaded_successfully:
            # Ensure annotations structure exists for this file (might be newly loaded)
            file_data = self.annotations.setdefault(self.current_file_path, {"entities": [], "relations": []})
            file_data.setdefault("entities", [])
            file_data.setdefault("relations", [])

            # Populate UI lists and apply highlighting
            self.update_entities_list() # Must happen before relation list if using entity text map
            self.update_relations_list()
            self.apply_annotations_to_text() # Highlight entities in text

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
        # Remove all known entity tag highlights
        for tag in self.entity_tags:
            try:
                self.text_area.tag_remove(tag, "1.0", tk.END)
            except tk.TclError: pass # Ignore if tag doesn't exist
        # Remove selection highlight
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
        if self.current_file_index < len(self.files_list) - 1:
            self.load_file(self.current_file_index + 1)

    def load_previous_file(self):
        if self.current_file_index > 0:
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
                # Check if it actually became relative (doesn't start with .. on same drive, or is not full path on different drive)
                # This check is imperfect across OS/drives, but a basic attempt.
                # A more robust check might involve Pathlib's is_relative_to (Python 3.9+) or more complex os.path logic.
                # For simplicity, we'll try os.path.relpath and use it if it doesn't look like an absolute path or ../../ etc.
                # A safer bet might be to just store basenames if not in the same root tree.
                if not os.path.isabs(rel_path) and not rel_path.startswith(('..'+os.sep, '..'+'/')):
                    key = rel_path.replace('\\', '/') # Use forward slashes for consistency
                else: # Fallback to basename if it seems outside the save hierarchy
                     key = os.path.basename(file_path)
            except ValueError: # Handle different drives on Windows
                key = os.path.basename(file_path)
            except Exception as e:
                print(f"Warning: Error calculating relative path for {file_path} relative to {save_dir}. Using basename. Error: {e}")
                key = os.path.basename(file_path)

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


    # --- NEW: Session Save/Load ---
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

        # Prepare session data
        session_data = {
            "version": SESSION_FILE_VERSION,
            "files_list": self.files_list, # Store full paths
            "current_file_index": self.current_file_index,
            "entity_tags": self.entity_tags,
            "relation_types": self.relation_types,
            "tag_colors": self.tag_colors,
            "annotations": self.annotations # Store with full paths as keys
            # Add other state variables if needed in the future (e.g., extend_to_word state)
             # "extend_to_word": self.extend_to_word.get()
        }

        # Write to JSON file
        try:
            with open(save_path, 'w', encoding='utf-8') as f:
                json.dump(session_data, f, indent=2, ensure_ascii=False)
            self.session_save_path = save_path # Remember path for next quick save
            self.status_var.set(f"Session saved to '{os.path.basename(save_path)}'")
            self.root.title(f"ANNIE - {os.path.basename(os.path.dirname(self.files_list[0]))} [{os.path.basename(save_path)}]") # Update title
        except Exception as e:
            messagebox.showerror("Save Session Error", f"Could not write session file:\n{e}", parent=self.root)
            self.status_var.set("Error saving session.")
            self.session_save_path = None # Failed, clear path

    def load_session(self):
        """Loads application state from a session file."""
        # --- Check for unsaved changes before discarding current state ---
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
        if not all(key in session_data for key in required_keys):
            messagebox.showerror("Load Session Error", "Session file is missing required data.", parent=self.root)
            return
        if not isinstance(session_data.get("files_list"), list) or \
           not isinstance(session_data.get("current_file_index"), int) or \
           not isinstance(session_data.get("annotations"), dict) or \
           not isinstance(session_data.get("entity_tags"), list) or \
           not isinstance(session_data.get("relation_types"), list) or \
           not isinstance(session_data.get("tag_colors"), dict):
            messagebox.showerror("Load Session Error", "Session file contains data with incorrect types.", parent=self.root)
            return

        # Version check
        loaded_version = session_data.get("version", "0.0")
        # Example: if loaded_version < "1.0": messagebox.showwarning(...)
        # print(f"Loading session version: {loaded_version}") # For debug

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
            self.annotations = session_data["annotations"]
            self.entity_tags = session_data["entity_tags"]
            self.relation_types = session_data["relation_types"]
            self.tag_colors = session_data["tag_colors"]
            # self.extend_to_word.set(session_data.get("extend_to_word", False)) # Example for loading other state

            self.session_save_path = load_path # Remember loaded session path

            # --- Update UI ---
            self.files_listbox.delete(0, tk.END)
            for file_path in self.files_list:
                # Indicate missing files in the listbox (optional)
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
            self._configure_text_tags() # Apply loaded colors
            self._configure_treeview_tags() # Ensure treeview styles are set

            # Load the correct file (if index is valid)
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
        # to the state when the session was last saved or loaded.
        # For now, just check if there are any files loaded and any annotations exist.
        # Or, if a session was loaded/saved, check if the current state differs.
        # Let's keep it simple: if files are loaded, assume potential changes.
        return bool(self.files_list) # Returns True if a directory/session is loaded

    def _on_closing(self):
        """Handles the window close event."""
        if self._has_unsaved_changes():
             if messagebox.askyesno("Exit Confirmation", "You have an active session.\nSave session before exiting?", parent=self.root):
                 self.save_session() # Attempt to save
                 # Check if save was successful (or cancelled) - tricky without return value check
                 # Assume save worked or user cancelled, then quit.
                 # If save failed, the error message would have popped up.
                 self.root.quit()
             else:
                 # User chose not to save
                 self.root.quit()
        else:
            # No unsaved changes detected
            self.root.quit()


    # --- Entity Annotation ---
    # Helper functions _spans_overlap_numeric, _is_overlapping_in_list, _is_overlapping_current_file
    def _spans_overlap_numeric(self, start1_line, start1_char, end1_line, end1_char,
                             start2_line, start2_char, end2_line, end2_char):
        """Checks if two spans, defined by line/char numbers, overlap."""
        span1_start = (start1_line, start1_char)
        span1_end = (end1_line, end1_char)
        span2_start = (start2_line, start2_char)
        span2_end = (end2_line, end2_char)
        if span1_start > span1_end: span1_start, span1_end = span1_end, span1_start
        if span2_start > span2_end: span2_start, span2_end = span2_end, span2_start
        is_disjoint = (span1_end <= span2_start) or (span1_start >= span2_end)
        return not is_disjoint

    def _is_overlapping_in_list(self, start_line, start_char, end_line, end_char, existing_entities_list):
        """Checks if the given span overlaps with any entity in the provided list."""
        for ann in existing_entities_list:
            if not all(k in ann for k in ['start_line', 'start_char', 'end_line', 'end_char']):
                print(f"Warning: Skipping overlap check against entity {ann.get('id','N/A')} missing position.")
                continue
            if self._spans_overlap_numeric(
                start_line, start_char, end_line, end_char,
                ann['start_line'], ann['start_char'], ann['end_line'], ann['end_char']
            ):
                return True # Overlap found
        return False # No overlap found

    def _is_overlapping_current_file(self, start_line, start_char, end_line, end_char):
        """Checks if the given span overlaps with existing ENTITIES in the *currently loaded* file's data."""
        if not self.current_file_path: return False # No file loaded
        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        if not entities: return False
        return self._is_overlapping_in_list(start_line, start_char, end_line, end_char, entities)

    def annotate_selection(self):
        """Annotates the selected text in the text_area as an entity."""
        if not self.current_file_path:
            messagebox.showinfo("Info", "Please load a file first.", parent=self.root)
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

            start_line, start_char = map(int, start_pos.split('.'))
            end_line, end_char = map(int, end_pos.split('.'))
            tag = self.selected_entity_tag.get()
            if not tag:
                messagebox.showwarning("Warning", "No entity tag selected.", parent=self.root)
                return

            if self._is_overlapping_current_file(start_line, start_char, end_line, end_char):
                messagebox.showwarning("Overlap Detected", "The selected text overlaps with an existing entity.", parent=self.root)
                return

            file_data = self.annotations.setdefault(self.current_file_path, {"entities": [], "relations": []})
            entities_list = file_data.setdefault("entities", [])

            entity_id = uuid.uuid4().hex
            annotation = {
                'id': entity_id, 'start_line': start_line, 'start_char': start_char,
                'end_line': end_line, 'end_char': end_char, 'text': selected_text, 'tag': tag
            }
            entities_list.append(annotation)

            # Apply visual tag
            if tag not in self.text_area.tag_names(): self._configure_text_tags()
            if tag in self.text_area.tag_names(): self.text_area.tag_add(tag, start_pos, end_pos)
            else: print(f"Warning: Could not apply unconfigured tag '{tag}'")

            self.update_entities_list() # Update list display

            # Select new entity in list
            self.root.update_idletasks()
            try:
                if self.entities_tree.exists(entity_id):
                    self.entities_tree.selection_set(entity_id)
                    self.entities_tree.focus(entity_id)
                    self.entities_tree.see(entity_id)
            except Exception as e: print(f"Error selecting new entity {entity_id}: {e}")

            status_text = f"Annotated: '{selected_text[:30].replace(os.linesep, ' ')}...' as {tag}"
            self.status_var.set(status_text)
            self._update_button_states()

        except tk.TclError as e:
            if "text doesn't contain selection" in str(e).lower():
                messagebox.showinfo("Info", "Please select text to annotate.", parent=self.root)
            else: messagebox.showerror("Annotation Error", f"A Tkinter error occurred:\n{e}", parent=self.root)
        except Exception as e: messagebox.showerror("Annotation Error", f"An unexpected error occurred:\n{e}", parent=self.root)

    def remove_entity_annotation(self):
        """Removes selected entities and their associated relations."""
        selected_iids = self.entities_tree.selection()
        if not selected_iids:
            messagebox.showinfo("Info", "Select one or more entities to remove.", parent=self.root)
            return
        if not self.current_file_path or self.current_file_path not in self.annotations:
            messagebox.showerror("Error", "Cannot remove entity: No file/annotations.", parent=self.root)
            return

        confirm = messagebox.askyesno("Confirm Removal",
            f"Remove {len(selected_iids)} entities?\nWARNING: This removes associated relations.", parent=self.root)
        if not confirm: return

        file_data = self.annotations.get(self.current_file_path, {})
        entities = file_data.get("entities", [])
        relations = file_data.get("relations", [])

        removed_entity_count = 0
        relations_to_remove_ids = set()
        entities_remaining = []

        for entity in entities:
            entity_id = entity.get('id')
            if entity_id in selected_iids:
                removed_entity_count += 1
                # Remove highlight (best effort)
                try:
                    start_pos = f"{entity['start_line']}.{entity['start_char']}"
                    end_pos = f"{entity['end_line']}.{entity['end_char']}"
                    tag = entity.get('tag')
                    if tag and tag in self.entity_tags and self.text_area.cget('state') == tk.NORMAL:
                         self.text_area.tag_remove(tag, start_pos, end_pos)
                except Exception: pass # Ignore errors removing tag

                # Mark associated relations
                if relations:
                    for relation in relations:
                        relation_id = relation.get('id')
                        if not relation_id: continue
                        if relation.get('head_id') == entity_id or relation.get('tail_id') == entity_id:
                            relations_to_remove_ids.add(relation_id)
            else:
                entities_remaining.append(entity) # Keep this one

        # Filter relations
        relations_remaining = [rel for rel in relations if rel.get('id') not in relations_to_remove_ids] if relations else []
        removed_relation_count = (len(relations) if relations else 0) - len(relations_remaining)

        # Update data structure
        self.annotations[self.current_file_path]["entities"] = entities_remaining
        self.annotations[self.current_file_path]["relations"] = relations_remaining

        # Refresh UI
        self.update_entities_list()
        self.update_relations_list()
        self.apply_annotations_to_text() # Re-apply remaining highlights

        self.status_var.set(f"Removed {removed_entity_count} entities, {removed_relation_count} relations.")
        self._update_button_states()

    def merge_selected_entities(self):
        """Merges selected entities in the list to share the same ID."""
        selected_iids = self.entities_tree.selection()
        if len(selected_iids) < 2:
            messagebox.showinfo("Info", "Select 2+ entities to merge.", parent=self.root)
            return
        if not self.current_file_path or self.current_file_path not in self.annotations:
            messagebox.showerror("Error", "Cannot merge: No file/annotations.", parent=self.root)
            return

        confirm = messagebox.askyesno("Confirm Merge",
            f"Merge {len(selected_iids)} entities?\nOne ID (earliest occurrence) will be used for all.\nRelations will be updated. Duplicate relations removed.", parent=self.root)
        if not confirm:
            self.status_var.set("Merge cancelled.")
            return

        file_data = self.annotations[self.current_file_path]
        entities = file_data.get("entities", [])
        relations = file_data.get("relations", [])

        # Find entity data for selected iids, ensure position data exists
        selected_entities_data = []
        found_ids = set()
        for entity in entities:
             eid = entity.get('id')
             if eid in selected_iids and eid not in found_ids: # Process each selected ID only once
                 if all(k in entity for k in ['start_line', 'start_char']):
                      selected_entities_data.append(entity)
                      found_ids.add(eid)
                 else:
                      print(f"Warning: Skipping entity {eid} in merge - missing position.")

        if len(selected_entities_data) < 2:
            messagebox.showerror("Error", "Need at least two valid entities with position data to merge.", parent=self.root)
            return

        # Sort by position to find canonical ID
        selected_entities_data.sort(key=lambda e: (e.get('start_line', 0), e.get('start_char', 0)))
        canonical_entity = selected_entities_data[0]
        canonical_id = canonical_entity.get('id')
        if not canonical_id:
            messagebox.showerror("Error", "Failed to determine canonical ID.", parent=self.root)
            return

        ids_to_merge_away = {e.get('id') for e in selected_entities_data if e.get('id') != canonical_id and e.get('id')}
        if not ids_to_merge_away:
            messagebox.showinfo("Info", "Selected entities already share the same ID or only one valid entity found.", parent=self.root)
            return

        modified_entity_count = 0
        modified_relation_count = 0

        # 1. Update Entity IDs
        for i, entity in enumerate(entities):
            if entity.get('id') in ids_to_merge_away:
                entities[i]['id'] = canonical_id
                modified_entity_count += 1

        # 2. Update Relation IDs
        if relations:
            for i, rel in enumerate(relations):
                relation_modified = False
                if rel.get('head_id') in ids_to_merge_away:
                    relations[i]['head_id'] = canonical_id
                    relation_modified = True
                if rel.get('tail_id') in ids_to_merge_away:
                    relations[i]['tail_id'] = canonical_id
                    relation_modified = True
                if relation_modified: modified_relation_count += 1

        # 3. Remove duplicate relations potentially created by merge
        removed_duplicates = 0
        if relations and modified_relation_count > 0: # Only check if changes might have occurred
            unique_relations = []
            seen_signatures = set() # (head_id, tail_id, type)
            for rel in relations:
                # Ignore self-loops if they arise? Current logic keeps them.
                # if rel.get('head_id') == rel.get('tail_id'): continue # Optional: remove self-loops
                sig = (rel.get('head_id'), rel.get('tail_id'), rel.get('type'))
                if sig not in seen_signatures:
                    seen_signatures.add(sig)
                    unique_relations.append(rel)
                else:
                    removed_duplicates += 1
                    # print(f"Info: Removing duplicate relation: {sig}")

            if removed_duplicates > 0:
                 self.annotations[self.current_file_path]["relations"] = unique_relations


        # --- Update UI ---
        self.update_entities_list() # Will re-render with 'merged' tag
        self.update_relations_list() # Will show updated head/tail

        # Re-select the items that now share the canonical ID
        self.root.update_idletasks()
        try:
            self.entities_tree.selection_set([]) # Clear selection
            items_to_reselect = []
            for item_iid in self.entities_tree.get_children(""):
                # Check the 'ID' value stored in the treeview item (index 0)
                item_values = self.entities_tree.item(item_iid, 'values')
                if item_values and item_values[0] == canonical_id:
                    items_to_reselect.append(item_iid)

            if items_to_reselect:
                self.entities_tree.selection_set(items_to_reselect)
                self.entities_tree.focus(items_to_reselect[0])
                self.entities_tree.see(items_to_reselect[0])
        except Exception as e: print(f"Warning: Error re-selecting merged entities: {e}")

        # Update status
        status_msg = f"Merged {len(selected_iids)} entities to ID {canonical_id[:6]}.... Updated {modified_relation_count} relations."
        if removed_duplicates > 0: status_msg += f" Removed {removed_duplicates} duplicates."
        self.status_var.set(status_msg)
        self._update_button_states()


    def apply_annotations_to_text(self):
        """Applies highlighting for all ENTITIES of the current file."""
        if not self.current_file_path or self.text_area.cget('state') == tk.DISABLED:
            return # Don't try if no file or text area is disabled

        original_state = self.text_area.cget('state')
        if original_state == tk.DISABLED: self.text_area.config(state=tk.NORMAL)

        # Remove all existing entity tags first
        for tag in self.entity_tags:
            try: self.text_area.tag_remove(tag, "1.0", tk.END)
            except tk.TclError: pass

        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        sorted_entities = sorted(entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0)))

        # Re-apply tags
        for ann in sorted_entities:
            try:
                start_pos = f"{ann['start_line']}.{ann['start_char']}"
                end_pos = f"{ann['end_line']}.{ann['end_char']}"
                tag = ann.get('tag')

                if tag and tag in self.entity_tags:
                    # Ensure tag is configured (might be newly loaded/added)
                    if tag not in self.text_area.tag_names(): self._configure_text_tags()
                    # Apply if configured
                    if tag in self.text_area.tag_names(): self.text_area.tag_add(tag, start_pos, end_pos)
                    else: print(f"Warning: Entity {ann.get('id','N/A')} tag '{tag}' unconfigurable.")
                elif tag: print(f"Warning: Entity {ann.get('id','N/A')} unknown tag '{tag}'.")
            except Exception as e: print(f"Warning: Error applying tag for entity {ann.get('id','N/A')}: {e}")

        self.text_area.config(state=original_state) # Restore original state


    def update_entities_list(self):
        """Updates the Entities Treeview with entities for the current file."""
        try: self.entities_tree.delete(*self.entities_tree.get_children())
        except Exception: pass

        if not self.current_file_path: # Handle case where file loading failed or no file loaded
            self._update_button_states()
            return

        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        if not entities:
            self.selected_entity_ids_for_relation = [] # Ensure clear if list empty
            self._update_button_states()
            return

        sorted_entities = sorted(entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0)))

        # Count ID occurrences for 'merged' tag
        entity_id_counts = {}
        for ann in sorted_entities:
            entity_id = ann.get('id')
            if entity_id: entity_id_counts[entity_id] = entity_id_counts.get(entity_id, 0) + 1

        # Populate tree
        for ann in sorted_entities:
            entity_id = ann.get('id')
            if not entity_id: continue # Skip invalid data

            try:
                start_pos_str = f"{ann['start_line']}.{ann['start_char']}"
                end_pos_str = f"{ann['end_line']}.{ann['end_char']}"
                full_text = ann.get('text', '')
                display_text = full_text.replace(os.linesep, ' ').replace('\n', ' ').replace('\r', '')[:60]
                if len(full_text) > 60: display_text += "..."
                tag = ann.get('tag', 'N/A')

                # Apply 'merged' tag if needed
                treeview_tags = ('merged',) if entity_id_counts.get(entity_id, 0) > 1 else ()

                # Insert with entity ID as iid and also in the hidden 'ID' column value
                self.entities_tree.insert("", tk.END, iid=entity_id,
                    values=(entity_id, start_pos_str, end_pos_str, display_text, tag),
                    tags=treeview_tags
                )
            except Exception as e: print(f"Error adding entity {entity_id} to list: {e}")

        self.selected_entity_ids_for_relation = [] # Clear selection state on list update
        self._update_button_states()


    def on_entity_select(self, event):
        """Handles selection changes in the Entities Treeview."""
        selected_iids = self.entities_tree.selection()
        self.selected_entity_ids_for_relation = list(selected_iids)

        # Highlight corresponding text spans
        if self.text_area.cget('state') == tk.NORMAL:
            self.text_area.tag_remove(tk.SEL, "1.0", tk.END) # Remove previous selection
            entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
            first_entity_pos = None

            for iid in selected_iids:
                # Find the specific entity data for this iid
                entity_data = next((e for e in entities if e.get('id') == iid), None)
                if entity_data:
                    try:
                        start_pos = f"{entity_data['start_line']}.{entity_data['start_char']}"
                        end_pos = f"{entity_data['end_line']}.{entity_data['end_char']}"
                        self.text_area.tag_add(tk.SEL, start_pos, end_pos)
                        if first_entity_pos is None: first_entity_pos = start_pos
                    except Exception as e: print(f"Warning: Error highlighting entity {iid}: {e}")

            # Scroll to first selected entity
            if first_entity_pos:
                try: self.text_area.see(first_entity_pos)
                except tk.TclError as e: print(f"Warning: Error scrolling to entity: {e}")

        self._update_button_states() # Update buttons based on selection


    # --- Relation Annotation ---
    def add_relation(self):
        """Adds a relation between the two selected entities (Head -> Tail)."""
        if len(self.selected_entity_ids_for_relation) != 2:
            messagebox.showerror("Selection Error", "Select exactly TWO entities (Head first, then Tail).", parent=self.root)
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

        # Check for duplicates
        if any(r.get('head_id') == head_id and r.get('tail_id') == tail_id and r.get('type') == relation_type for r in relations_list):
            messagebox.showwarning("Duplicate Relation", "This exact relation already exists.", parent=self.root)
            return

        relation_id = uuid.uuid4().hex
        new_relation = {"id": relation_id, "type": relation_type, "head_id": head_id, "tail_id": tail_id}
        relations_list.append(new_relation)
        self.update_relations_list()

        # Select new relation
        self.root.update_idletasks()
        try:
            if self.relations_tree.exists(relation_id):
                self.relations_tree.selection_set(relation_id)
                self.relations_tree.focus(relation_id)
                self.relations_tree.see(relation_id)
        except Exception as e: print(f"Error selecting new relation: {e}")

        self.status_var.set(f"Added Relation: {relation_type} ({head_id[:4]}... -> {tail_id[:4]}...)")

    def flip_selected_relation(self):
        """Flips the Head and Tail entities for the selected relation."""
        selected_iids = self.relations_tree.selection()
        if len(selected_iids) != 1: return # Should be disabled if not 1

        relation_id_to_flip = selected_iids[0]
        relations = self.annotations.get(self.current_file_path, {}).get("relations")
        if not relations: return # No relations to flip

        found = False
        for i, rel in enumerate(relations):
            if rel.get('id') == relation_id_to_flip:
                current_head, current_tail = rel.get('head_id'), rel.get('tail_id')
                if current_head and current_tail:
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
            except Exception as e: print(f"Warning: Error re-selecting flipped relation: {e}")
            self.status_var.set("Relation Head/Tail flipped.")
        # else: messagebox.showwarning("Not Found", "Could not find selected relation.", parent=self.root) # Should not happen


    def remove_relation_annotation(self):
        """Removes the selected relation from the Relations list."""
        selected_iids = self.relations_tree.selection()
        if len(selected_iids) != 1: return # Should be disabled if not 1

        relation_id_to_remove = selected_iids[0]
        relations = self.annotations.get(self.current_file_path, {}).get("relations")
        if not relations: return # No relations to remove

        original_length = len(relations)
        self.annotations[self.current_file_path]["relations"] = [
            rel for rel in relations if rel.get('id') != relation_id_to_remove
        ]

        if len(self.annotations[self.current_file_path]["relations"]) < original_length:
            self.update_relations_list()
            self.status_var.set("Relation removed.")
        # else: messagebox.showwarning("Not Found", "Could not find selected relation.", parent=self.root) # Should not happen


    def update_relations_list(self):
        """Updates the Relations Treeview with relations for the current file."""
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

        # Build lookup map from ALL entities in this file (needed for Head/Tail text)
        # Crucially, handle merged entities: use the text from the *first* occurrence for display
        entity_display_map = {}
        processed_ids_for_map = set()
        # Sort entities by position to ensure we get the first occurrence's text for merged IDs
        sorted_entities_for_map = sorted(entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0)))
        for entity in sorted_entities_for_map:
             eid = entity.get('id')
             if eid and eid not in processed_ids_for_map:
                  etext = entity.get('text', 'N/A')
                  display_text = etext.replace(os.linesep, ' ').replace('\n',' ').replace('\r','')[:30]
                  if len(etext) > 30: display_text += "..."
                  # Optional: Add tag? display_text += f" [{entity.get('tag','?')}]"
                  entity_display_map[eid] = display_text
                  processed_ids_for_map.add(eid)


        sorted_relations = sorted(relations, key=lambda r: (r.get('type', ''), r.get('head_id','')))

        for rel in sorted_relations:
            rel_id, head_id, tail_id, rel_type = rel.get('id'), rel.get('head_id'), rel.get('tail_id'), rel.get('type')
            if not (rel_id and head_id and tail_id and rel_type): continue # Skip invalid

            head_text = entity_display_map.get(head_id, f"<ID: {head_id[:6]}...>")
            tail_text = entity_display_map.get(tail_id, f"<ID: {tail_id[:6]}...>")
            values_to_insert = (rel_id, head_text, rel_type, tail_text)

            try: self.relations_tree.insert("", tk.END, iid=rel_id, values=values_to_insert)
            except Exception as e: print(f"Error inserting relation {rel_id} into tree: {e}")

        self._update_button_states() # Update buttons after list refresh

    def on_relation_select(self, event):
        """Handles selection changes in the Relations Treeview."""
        # Primarily needed to update button states (Flip/Remove)
        self._update_button_states()


    # --- Propagation (Unchanged Logic, added parent=self.root to messageboxes) ---
    def propagate_annotations(self):
        """Propagate ENTITY annotations from the *current* file to ALL files."""
        if not self.current_file_path or not self.files_list:
            messagebox.showinfo("Info", "Load a directory first.", parent=self.root)
            return
        source_entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        if not source_entities:
            messagebox.showinfo("Info", "No entities in current file to propagate.", parent=self.root)
            return
        text_to_tag = {ann['text']: ann['tag'] for ann in source_entities if ann.get('text','').strip() and ann.get('tag')}
        if not text_to_tag:
            messagebox.showinfo("Info", "No valid text/tag pairs found to propagate.", parent=self.root)
            return

        confirm = messagebox.askyesno("Confirm Propagation (Current File)",
            f"Search for {len(text_to_tag)} text/tag pairs from '{os.path.basename(self.current_file_path)}' "
            f"across all {len(self.files_list)} files?\n\n"
            f"WARNING: Adds new annotations. Skips overlaps. Relations not propagated.", parent=self.root)
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
            title="Select Dictionary File (Text<TAB/SPACE>Tag)",
            filetypes=[("Text files", "*.txt"), ("TSV files", "*.tsv"), ("All files", "*.*")],
            parent=self.root
        )
        if not dict_path: return

        dictionary_mapping = {}
        lines_read, valid_entries, skipped_lines = 0, 0, 0
        invalid_tags_found = set()
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

                    entity_text, label = parts[0].strip(), parts[1].strip()
                    if not entity_text: skipped_lines += 1; continue

                    if label in self.entity_tags:
                        if entity_text in dictionary_mapping and dictionary_mapping[entity_text] != label:
                            print(f"Warning: Dict line {line_num}: Text '{entity_text}' redefined tag. Using last.")
                        dictionary_mapping[entity_text] = label
                        valid_entries += 1 # Count only when adding/overwriting valid entry
                    else:
                        invalid_tags_found.add(label)
                        skipped_lines += 1 # Count as skipped if tag invalid
            # Adjust valid count if overwrites happened (tricky without tracking adds vs overwrites)
            # For simplicity, valid_entries counts lines processed with valid tags.
            valid_entries = len(dictionary_mapping) # More accurate: final count of unique texts mapped

        except Exception as e:
            messagebox.showerror("Dictionary Read Error", f"Failed to read dictionary:\n{e}", parent=self.root)
            return

        if not dictionary_mapping:
             msg = f"Finished reading dictionary '{os.path.basename(dict_path)}'.\n"
             msg += f"Read {lines_read} lines. Found 0 valid entries.\n"
             if invalid_tags_found: msg += f"Skipped lines due to unrecognized tags (e.g., {', '.join(list(invalid_tags_found)[:5])}...).\n"
             if skipped_lines > len(invalid_tags_found): msg += f"Other lines skipped (formatting/empty)."
             messagebox.showinfo("Dictionary Results", msg, parent=self.root)
             return

        confirm_msg = f"Dictionary '{os.path.basename(dict_path)}' loaded.\n"
        confirm_msg += f"- Found {valid_entries} unique entries with valid tags.\n"
        confirm_msg += f"- Read {lines_read} total lines (skipped {skipped_lines}).\n"
        if invalid_tags_found: confirm_msg += f"- Example skipped tags: {', '.join(list(invalid_tags_found)[:5])}{'...' if len(invalid_tags_found)>5 else ''}\n"
        confirm_msg += f"\nPropagate these {valid_entries} annotations across {len(self.files_list)} files?\n\n(Skips overlaps. Relations not affected.)"

        confirm = messagebox.askyesno("Confirm Dictionary Propagation", confirm_msg, parent=self.root)
        if not confirm:
            self.status_var.set("Dictionary propagation cancelled.")
            return
        self._perform_propagation(dictionary_mapping, "Dictionary Propagation")


    def _perform_propagation(self, text_to_tag_map, source_description):
        """COMMON entity propagation logic across all files."""
        propagated_count = 0
        affected_files_count = 0
        extend_option = self.extend_to_word.get()
        current_file_was_modified = False

        self.status_var.set(f"Starting {source_description}...")
        self.root.update_idletasks()

        sorted_texts_to_find = sorted(text_to_tag_map.keys(), key=len, reverse=True)

        for i, file_path in enumerate(self.files_list):
            file_modified_in_this_run = False
            if (i + 1) % 10 == 0 or i == len(self.files_list) - 1:
                self.status_var.set(f"{source_description}: Processing file {i+1}/{len(self.files_list)}...")
                self.root.update_idletasks()

            # Skip processing if file was reported missing during session load
            if not os.path.isfile(file_path):
                print(f"Info: Skipping propagation for missing file: {file_path}")
                continue

            try:
                with open(file_path, 'r', encoding='utf-8') as f: content = f.read()
                lines = content.splitlines() # Handles \n, \r, \r\n

                file_data = self.annotations.setdefault(file_path, {"entities": [], "relations": []})
                target_entities_list = file_data.setdefault("entities", [])

                # Create temporary list of spans already annotated *in this file* to check against
                # Store as (start_line, start_char, end_line, end_char) tuples for faster checking
                existing_spans = set()
                for ann in target_entities_list:
                    if all(k in ann for k in ['start_line', 'start_char', 'end_line', 'end_char']):
                         existing_spans.add((ann['start_line'], ann['start_char'], ann['end_line'], ann['end_char']))


                newly_added_spans_this_file = set() # Track spans added *during this propagation* for overlap checks

                for text_to_find in sorted_texts_to_find:
                    tag_to_apply = text_to_tag_map[text_to_find]
                    if not text_to_find: continue # Skip empty

                    for line_num, line in enumerate(lines, 1): # tk.Text uses 1-based lines
                        start_char_search = 0
                        while True:
                            found_char_index = line.find(text_to_find, start_char_search)
                            if found_char_index == -1: break # Not in rest of line

                            match_start_char = found_char_index
                            match_end_char = found_char_index + len(text_to_find)
                            annotated_text = text_to_find

                            # Extend to word boundaries if option checked
                            if extend_option:
                                word_start_char, word_end_char = match_start_char, match_end_char
                                while word_start_char > 0 and line[word_start_char - 1].isalnum(): word_start_char -= 1
                                while word_end_char < len(line) and line[word_end_char].isalnum(): word_end_char += 1
                                if word_start_char != match_start_char or word_end_char != match_end_char:
                                    match_start_char = word_start_char
                                    match_end_char = word_end_char
                                    annotated_text = line[match_start_char:match_end_char]

                            # Use numeric span for overlap check
                            current_span = (line_num, match_start_char, line_num, match_end_char)

                            # Check overlap against BOTH pre-existing and newly added spans in *this file*
                            overlap = False
                            # Check against pre-existing
                            for existing_span in existing_spans:
                                if self._spans_overlap_numeric(*current_span, *existing_span):
                                    overlap = True; break
                            if overlap:
                                start_char_search = match_end_char # Move past overlap
                                continue # Skip this match
                            # Check against newly added in this run
                            for new_span in newly_added_spans_this_file:
                                if self._spans_overlap_numeric(*current_span, *new_span):
                                    overlap = True; break

                            # Add annotation if no overlap found
                            if not overlap:
                                entity_id = uuid.uuid4().hex
                                new_annotation = {
                                    'id': entity_id, 'start_line': line_num, 'start_char': match_start_char,
                                    'end_line': line_num, 'end_char': match_end_char,
                                    'text': annotated_text, 'tag': tag_to_apply
                                }
                                target_entities_list.append(new_annotation)
                                newly_added_spans_this_file.add(current_span) # Track added span
                                propagated_count += 1
                                file_modified_in_this_run = True
                                if file_path == self.current_file_path: current_file_was_modified = True

                            # Advance search position past the *original* match end, or extended end?
                            # Let's advance past the extended end to avoid issues if extension creates overlap possibility.
                            start_char_search = match_end_char
                            if start_char_search <= found_char_index: # Safety break
                                start_char_search = found_char_index + 1

            except Exception as e: print(f"ERROR processing file '{os.path.basename(file_path)}' during propagation:\n{str(e)}")

            if file_modified_in_this_run: affected_files_count += 1

        # Post-propagation
        if current_file_was_modified:
            self.update_entities_list()
            self.apply_annotations_to_text()
        self._update_button_states()

        summary = f"{source_description} complete.\nAdded {propagated_count} new entities across {affected_files_count} files."
        if extend_option: summary += "\n('Extend to whole word' was enabled)"
        messagebox.showinfo("Propagation Results", summary, parent=self.root)
        self.status_var.set(f"{source_description} finished. Added {propagated_count} entities.")



    # --- Tag/Type Management ---
    def _manage_items(self, item_type_name, current_items_list, update_combobox_func):
        """Generic modal window for managing tags/types."""
        window = tk.Toplevel(self.root)
        window.title(f"Manage {item_type_name}")
        window.geometry("350x400"); window.resizable(False, False)
        window.transient(self.root); window.grab_set()

        list_frame = tk.Frame(window); list_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(10, 0))
        tk.Label(list_frame, text=f"Current {item_type_name}:").pack(anchor=tk.W)
        scrollbar = tk.Scrollbar(list_frame); scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        listbox = tk.Listbox(list_frame, yscrollcommand=scrollbar.set, exportselection=False)

        # Populate listbox with current items
        for item in current_items_list:
             listbox.insert(tk.END, item)
             if item_type_name == "Entity Tags":
                  color = self.get_color_for_tag(item)
                  try: listbox.itemconfig(tk.END, {'bg': color})
                  except: pass # Ignore color errors

        listbox.pack(fill=tk.BOTH, expand=True)
        scrollbar.config(command=listbox.yview)

        controls_frame = tk.Frame(window); controls_frame.pack(fill=tk.X, padx=10, pady=10)
        item_var = tk.StringVar()
        item_entry = tk.Entry(controls_frame, textvariable=item_var, width=20)
        item_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 5))

        def add_item():
            item = item_var.get().strip()
            if item:
                existing_lower = [listbox.get(i).lower() for i in range(listbox.size())]
                if item.lower() not in existing_lower:
                    listbox.insert(tk.END, item)
                    if item_type_name == "Entity Tags":
                        color = self.get_color_for_tag(item) # Get/generate color
                        try: listbox.itemconfig(tk.END, {'bg': color})
                        except: pass
                    item_var.set(""); listbox.see(tk.END)
                else: messagebox.showwarning("Duplicate", f"'{item}' already exists.", parent=window)
            item_entry.focus_set()
        item_entry.bind("<Return>", lambda event: add_item())

        add_btn = tk.Button(controls_frame, text="Add", width=7, command=add_item)
        add_btn.pack(side=tk.LEFT, padx=5)

        def remove_item():
            indices = listbox.curselection()
            if indices:
                 # Prompt for confirmation if removing tags associated with existing annotations? (Complex)
                 # For now, just remove. User is warned implicitly by potential loss of highlighting.
                 for index in reversed(indices): listbox.delete(index)
            else: messagebox.showwarning("No Selection", "Select item(s) to remove.", parent=window)

        remove_btn = tk.Button(controls_frame, text="Remove", width=7, command=remove_item)
        remove_btn.pack(side=tk.LEFT)

        button_frame = tk.Frame(window); button_frame.pack(fill=tk.X, padx=10, pady=(0, 10))

        def save_changes():
            new_items = list(listbox.get(0, tk.END))
            # Prevent removing *all* items? Maybe allow it for relations, but not entities?
            # Let's allow removing all for now, combobox update handles empty list.
            # if not new_items:
            #      messagebox.showwarning("Warning", f"Cannot remove all {item_type_name}.", parent=window)
            #      return

            if set(new_items) != set(current_items_list): # Check if set contents changed
                 removed_items = set(current_items_list) - set(new_items)
                 # --- Warning about existing annotations losing tags ---
                 if item_type_name == "Entity Tags" and removed_items:
                     # Check if any annotations actually use the tags being removed (across all files)
                     tags_in_use = set()
                     for data in self.annotations.values():
                         for entity in data.get("entities", []):
                             if entity.get('tag') in removed_items:
                                 tags_in_use.add(entity['tag'])
                     if tags_in_use:
                         if not messagebox.askyesno("Confirm Tag Removal",
                             f"You are removing tags that are currently used by annotations:\n"
                             f"- {', '.join(list(tags_in_use))}\n\n"
                             f"Annotations with these tags will remain but lose their highlighting and assigned tag.\n"
                             f"Continue?", parent=window):
                             return # User cancelled save

                 # Apply Changes
                 current_items_list[:] = new_items # Update original list in place
                 update_combobox_func() # Update the UI combobox

                 if item_type_name == "Entity Tags":
                      # Remove configurations for deleted tags
                      for removed_tag in removed_items:
                          try: self.text_area.tag_delete(removed_tag)
                          except: pass # Ignore error if tag didn't exist
                          if removed_tag in self.tag_colors: del self.tag_colors[removed_tag] # Remove color mapping

                      # Ensure remaining/new tags are configured
                      self._configure_text_tags()
                      # Re-apply highlights (will skip removed tags) and update lists
                      self.apply_annotations_to_text()
                      self.update_entities_list() # Tag column might change for remaining entities
                 elif item_type_name == "Relation Types":
                      # If relation types are removed, update the relation list display
                      # (though annotations themselves aren't deleted here)
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
        # Check available themes: print(style.theme_names())
        available_themes = style.theme_names()
        if 'clam' in available_themes: style.theme_use('clam')
        elif 'alt' in available_themes: style.theme_use('alt')
        else: style.theme_use('default') # Fallback
    except tk.TclError:
        print("ttk themes not available or failed to set.") # Continue with default Tk look

    app = TextAnnotator(root)
    root.mainloop()

if __name__ == "__main__":
    main()
