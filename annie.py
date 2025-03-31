"""
ANNIE: Annotation Interface for Named-entity & Information Extraction.
Allows loading text files, annotating text spans (entities) with tags,
and annotating directed relations between entities.
Includes basic propagation for entities and management for tags/relation types.
Adds dictionary-based entity propagation, relation flipping, and entity merging.
"""

import os
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import json
from pathlib import Path
import uuid  # For unique IDs
import itertools # For cycling through colors
import re # For word boundary checking if needed

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
        self.root.title("ANNIE - Annotation Interface for Named-entity & Information Extraction")
        # Increased size to better accommodate all elements
        self.root.geometry("1200x850")

        # --- Core Data ---
        self.current_file_path = None
        self.files_list = []
        self.current_file_index = -1
        # Main annotation data structure:
        # { "full/path/to/file.txt": {"entities": [entity_dict,...], "relations": [relation_dict,...]}, ... }
        self.annotations = {}

        # --- Entity Tagging Configuration ---
        self.entity_tags = ["Person", "Organization", "Location", "Date", "Other"]
        self.selected_entity_tag = tk.StringVar(value=self.entity_tags[0] if self.entity_tags else "")
        self.extend_to_word = tk.BooleanVar(value=False) # For entity propagation

        # --- Relation Tagging Configuration ---
        # Example relations, can be managed via Settings menu
        self.relation_types = ["spouse_of", "works_at", "located_in", "born_on", "produces"]
        self.selected_relation_type = tk.StringVar(value=self.relation_types[0] if self.relation_types else "")

        # --- UI State ---
        # Stores UUIDs of entities selected in the entities_tree, used for creating relations
        self.selected_entity_ids_for_relation = []

        # --- Colors ---
        # Predefined colors for common tags
        self.tag_colors = {
            "Person": "#ffcccc", "Organization": "#ccffcc", "Location": "#ccccff",
            "Date": "#ffffcc", "Other": "#ccffff"
        }
        # Fallback colors for new tags added via settings, cycles through this list
        self.color_cycle = itertools.cycle([
            "#e6e6fa", "#ffe4e1", "#f0fff0", "#fffacd", "#add8e6",
            "#f5f5dc", "#d3ffd3", "#fafad2", "#ffebcd", "#e0ffff"
        ])

        # --- Build UI ---
        self.create_menu()
        self.create_layout() # Call the corrected layout function

        # --- Status Bar ---
        self.status_var = tk.StringVar(value="Ready. Open a directory to start.")
        self.status_bar = tk.Label(self.root, textvariable=self.status_var, bd=1, relief=tk.SUNKEN, anchor=tk.W)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)

        # --- Initial UI Setup ---
        self._update_entity_tag_combobox()
        self._update_relation_type_combobox()
        self._configure_text_tags() # Apply initial tag colors
        self._configure_treeview_tags() # Configure treeview tags (e.g., for merging)
        self._update_button_states() # Set initial button enable/disable state


    # --- Menu Creation ---
    def create_menu(self):
        """Creates the main application menu bar."""
        menubar = tk.Menu(self.root)

        # File menu
        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Open Directory", command=self.load_directory)
        # Placeholder for Load Annotations feature
        # file_menu.add_command(label="Load Annotations", command=self.load_annotations_from_file) # To be implemented
        file_menu.add_command(label="Save Annotations", command=self.save_annotations)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.root.quit)
        menubar.add_cascade(label="File", menu=file_menu)

        # Settings menu
        settings_menu = tk.Menu(menubar, tearoff=0)
        settings_menu.add_command(label="Manage Entity Tags", command=self.manage_entity_tags)
        settings_menu.add_command(label="Manage Relation Types", command=self.manage_relation_types)
        settings_menu.add_separator() # Separator before the new option
        settings_menu.add_command(label="Load Dictionary & Propagate Entities", command=self.load_and_propagate_from_dictionary)
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
        # Adjusted packing for potentially more buttons
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
        # <<< NEW MERGE BUTTON >>>
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
        # Adjusted packing for potentially more buttons
        relation_controls_frame.pack(side=tk.LEFT, padx=(0, 5), pady=5, fill=tk.X, expand=True)

        tk.Label(relation_controls_frame, text="Type:").pack(side=tk.LEFT)
        self.relation_type_combobox = ttk.Combobox(relation_controls_frame, textvariable=self.selected_relation_type, values=self.relation_types, width=12, state="readonly")
        self.relation_type_combobox.pack(side=tk.LEFT, padx=5)
        self.add_relation_btn = tk.Button(relation_controls_frame, text="Add Relation (Head->Tail)", command=self.add_relation, state=tk.DISABLED, width=20) # Slightly reduced width
        self.add_relation_btn.pack(side=tk.LEFT, padx=(5, 2)) # Reduced right padx

        # <<< NEW FLIP BUTTON >>>
        self.flip_relation_btn = tk.Button(relation_controls_frame, text="Flip H/T", command=self.flip_selected_relation, state=tk.DISABLED, width=7)
        self.flip_relation_btn.pack(side=tk.LEFT, padx=2) # Added padding

        self.remove_relation_btn = tk.Button(relation_controls_frame, text="Remove Relation", command=self.remove_relation_annotation, state=tk.DISABLED, width=14) # Slightly reduced width
        self.remove_relation_btn.pack(side=tk.LEFT, padx=(2, 5)) # Reduced left padx


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
        # Explicitly defining the 'ID' column, even though not displayed by default, is needed for iid mapping
        self.entities_tree.column("ID", width=0, stretch=False) # Hide the ID column itself
        self.entities_tree.heading("Start", text="Start")
        self.entities_tree.heading("End", text="End")
        self.entities_tree.heading("Text", text="Text")
        self.entities_tree.heading("Tag", text="Tag")
        self.entities_tree.column("Start", width=70, anchor=tk.W, stretch=False)
        self.entities_tree.column("End", width=70, anchor=tk.W, stretch=False)
        self.entities_tree.column("Text", width=300, anchor=tk.W, stretch=True)
        self.entities_tree.column("Tag", width=100, anchor=tk.W, stretch=False)
        self.entities_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.entities_tree.bind("<<TreeviewSelect>>", self.on_entity_select)
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
            yscrollcommand=scrollbar_relations_y.set, selectmode='browse' # Keep browse (single select)
        )
        self.relations_tree.column("ID", width=0, stretch=False) # Hide ID column
        self.relations_tree.heading("Head", text="Head Entity")
        self.relations_tree.heading("Type", text="Relation Type")
        self.relations_tree.heading("Tail", text="Tail Entity")
        self.relations_tree.column("Head", width=250, anchor=tk.W, stretch=True)
        self.relations_tree.column("Type", width=120, anchor=tk.CENTER, stretch=False)
        self.relations_tree.column("Tail", width=250, anchor=tk.W, stretch=True)
        self.relations_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.relations_tree.bind("<<TreeviewSelect>>", self.on_relation_select)
        scrollbar_relations_y.config(command=self.relations_tree.yview)


    # --- Color and Tag Configuration ---
    def get_color_for_tag(self, tag):
        """Gets a color for a tag, generating one if not predefined."""
        if tag not in self.tag_colors:
            try:
                self.tag_colors[tag] = next(self.color_cycle)
            except Exception:
                # Fallback if cycle fails somehow
                self.tag_colors[tag] = "#cccccc"
        return self.tag_colors.get(tag, "#cccccc") # Default grey if tag somehow not found

    def _configure_text_tags(self):
        """Configures background colors for all known entity tags in the text area."""
        for tag in self.entity_tags:
            color = self.get_color_for_tag(tag)
            try:
                # Ensure tag exists before configuring
                self.text_area.tag_configure(tag, background=color)
            except tk.TclError as e:
                print(f"Warning: Could not configure text tag '{tag}': {e}")

    # <<< NEW METHOD >>>
    def _configure_treeview_tags(self):
        """Configures tags for styling the Treeview items (e.g., for merged entities)."""
        try:
            # Style for entities that have been merged (share an ID with others)
            self.entities_tree.tag_configure(
                'merged',
                foreground='grey',
                font=('TkDefaultFont', 9, 'italic') # Adjust font size/style as needed
            )
            # Add more tags here if needed in the future
        except tk.TclError as e:
            print(f"Warning: Could not configure Treeview tags: {e}")

    def _update_entity_tag_combobox(self):
        """Updates the values and state of the entity tag combobox."""
        self.entity_tag_combobox['values'] = self.entity_tags
        current_selection = self.selected_entity_tag.get()
        if not self.entity_tags:
            self.selected_entity_tag.set("")
            self.entity_tag_combobox.config(state=tk.DISABLED)
        # Set to first tag if current selection invalid OR if combobox is currently disabled
        elif current_selection not in self.entity_tags or self.entity_tag_combobox['state'] == tk.DISABLED:
            self.selected_entity_tag.set(self.entity_tags[0])
            self.entity_tag_combobox.config(state="readonly") # Ensure it's re-enabled
        else:
             # If selection is valid and combobox already enabled, just ensure it's readonly
             self.entity_tag_combobox.config(state="readonly")


    def _update_relation_type_combobox(self):
        """Updates the values and state of the relation type combobox."""
        self.relation_type_combobox['values'] = self.relation_types
        current_selection = self.selected_relation_type.get()
        if not self.relation_types:
            self.selected_relation_type.set("")
            self.relation_type_combobox.config(state=tk.DISABLED)
        elif current_selection not in self.relation_types or self.relation_type_combobox['state'] == tk.DISABLED:
            self.selected_relation_type.set(self.relation_types[0])
            self.relation_type_combobox.config(state="readonly")
        else:
             self.relation_type_combobox.config(state="readonly")

    # --- Button State Management ---
    def _update_button_states(self):
        """Enable/disable buttons based on current application state."""
        file_loaded = bool(self.current_file_path)
        has_files = bool(self.files_list)
        num_entities_selected = len(self.entities_tree.selection())
        num_relations_selected = len(self.relations_tree.selection()) # Get count of selected relations

        # File Navigation
        self.prev_btn.config(state=tk.NORMAL if has_files and self.current_file_index > 0 else tk.DISABLED)
        self.next_btn.config(state=tk.NORMAL if has_files and self.current_file_index < len(self.files_list) - 1 else tk.DISABLED)

        # Text Area
        # Enable text area only if a file is loaded. Use 'normal' state for editing.
        self.text_area.config(state=tk.NORMAL if file_loaded else tk.DISABLED)

        # Entity Buttons
        self.annotate_btn.config(state=tk.NORMAL if file_loaded and self.entity_tags else tk.DISABLED)
        self.remove_entity_btn.config(state=tk.NORMAL if num_entities_selected > 0 else tk.DISABLED)
        # <<< UPDATE MERGE BUTTON STATE >>>
        self.merge_entities_btn.config(state=tk.NORMAL if num_entities_selected >= 2 else tk.DISABLED) # Enable if 2 or more are selected
        can_propagate_current = file_loaded and self.annotations.get(self.current_file_path, {}).get("entities")
        self.propagate_btn.config(state=tk.NORMAL if can_propagate_current else tk.DISABLED)


        # Relation Buttons
        can_add_relation = num_entities_selected == 2 and self.relation_types
        self.add_relation_btn.config(state=tk.NORMAL if can_add_relation else tk.DISABLED)

        # <<< UPDATE FLIP/REMOVE BUTTON STATES >>>
        # Enable Flip and Remove only if *exactly one* relation is selected
        can_modify_relation = num_relations_selected == 1
        self.flip_relation_btn.config(state=tk.NORMAL if can_modify_relation else tk.DISABLED)
        self.remove_relation_btn.config(state=tk.NORMAL if can_modify_relation else tk.DISABLED)


    # --- File Handling ---
    def load_directory(self):
        """Opens a directory, lists .txt files, and loads the first one."""
        directory = filedialog.askdirectory(title="Select Directory with Text Files")
        if directory:
            self.files_list = []
            self.files_listbox.delete(0, tk.END)
            self.annotations = {} # Clear all annotations when loading new directory
            self.current_file_path = None
            self.current_file_index = -1
            self.clear_views() # Clear UI elements

            try:
                # Use Path for potentially better cross-platform handling if needed
                # p = Path(directory)
                # self.files_list = sorted([str(f) for f in p.glob('*.txt')])
                # Or stick to os for simplicity:
                for filename in sorted(os.listdir(directory)):
                    if filename.lower().endswith(".txt"):
                        full_path = os.path.join(directory, filename)
                        self.files_list.append(full_path)
                        self.files_listbox.insert(tk.END, filename) # Display only filename
            except OSError as e:
                 messagebox.showerror("Error Loading Directory", f"Could not read directory contents:\n{e}")
                 return # Stop if directory cannot be read

            if self.files_list:
                self.load_file(0) # Load the first file
                self.status_var.set(f"Loaded {len(self.files_list)} files from '{os.path.basename(directory)}'")
            else:
                self.status_var.set(f"No .txt files found in '{os.path.basename(directory)}'")
            self._update_button_states() # Update buttons after loading

    def load_file(self, index):
        """Loads the content and annotations for the file at the given index."""
        if not (0 <= index < len(self.files_list)):
            print(f"Warning: Invalid file index {index} requested.")
            return

        # Clear previous file's state before loading new one
        self.clear_views()

        self.current_file_index = index
        self.current_file_path = self.files_list[index]
        filename = os.path.basename(self.current_file_path)

        # Update listbox selection visually
        self.files_listbox.selection_clear(0, tk.END)
        self.files_listbox.selection_set(index)
        self.files_listbox.see(index) # Ensure selected item is visible

        # Load file content
        self.text_area.config(state=tk.NORMAL) # Temporarily enable to insert text
        self.text_area.delete(1.0, tk.END)
        file_loaded_successfully = False
        try:
            # Always use utf-8 for broader compatibility
            with open(self.current_file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                self.text_area.insert(tk.END, content)
            file_loaded_successfully = True
        except Exception as e:
            messagebox.showerror("Error Reading File", f"Failed to load file '{filename}':\n{str(e)}")
            self.text_area.config(state=tk.DISABLED) # Disable text area on error
            self.current_file_path = None # Reset state
            self.current_file_index = -1
            self.status_var.set(f"Error loading {filename}")
            file_loaded_successfully = False
            # Update buttons before returning
            self._update_button_states()
            return # Stop processing this file

        # If loaded successfully, load/apply annotations
        if file_loaded_successfully:
            # Ensure annotations structure exists for this file
            file_data = self.annotations.setdefault(self.current_file_path, {"entities": [], "relations": []})
            # Ensure lists exist within the structure
            file_data.setdefault("entities", [])
            file_data.setdefault("relations", [])

            # Populate UI lists and apply highlighting
            self.update_entities_list()
            self.update_relations_list()
            self.apply_annotations_to_text() # Highlight entities in text

            self.status_var.set(f"Loaded: {filename} ({index+1}/{len(self.files_list)})")

            # Reset undo stack for the new file
            self.text_area.edit_reset()
            # Keep text area editable after loading
            self.text_area.config(state=tk.NORMAL)

        # Always update button states after load attempt
        self._update_button_states()


    def clear_views(self):
        """Clears text area content, highlights, and annotation list Treeviews."""
        # Store original state to restore later if needed
        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL) # Enable to modify
        self.text_area.delete(1.0, tk.END)
        # Remove all known entity tag highlights
        for tag in self.entity_tags:
            try:
                 self.text_area.tag_remove(tag, "1.0", tk.END)
            except tk.TclError:
                 pass # Ignore if tag doesn't exist or causes error
        # Remove selection highlight
        try:
             self.text_area.tag_remove(tk.SEL, "1.0", tk.END)
        except tk.TclError:
             pass
        # Restore original state (usually DISABLED if no file was loaded, NORMAL if file was loaded)
        self.text_area.config(state=original_state if self.current_file_path else tk.DISABLED)

        # Clear Treeviews safely
        try:
             self.entities_tree.delete(*self.entities_tree.get_children())
        except Exception as e:
             print(f"Info: Error clearing entities tree (might be empty): {e}")
        try:
             self.relations_tree.delete(*self.relations_tree.get_children())
        except Exception as e:
             print(f"Info: Error clearing relations tree (might be empty): {e}")

        # Reset selection state variable used for relations
        self.selected_entity_ids_for_relation = []


    def load_next_file(self):
        if self.current_file_index < len(self.files_list) - 1:
            self.load_file(self.current_file_index + 1)

    def load_previous_file(self):
        if self.current_file_index > 0:
            self.load_file(self.current_file_index - 1)

    def on_file_select(self, event):
        # Need the widget that triggered the event if used with multiple listboxes
        # widget = event.widget
        selected_indices = self.files_listbox.curselection()
        if selected_indices:
            index = selected_indices[0]
            # Only load if the selection changed to a different file
            if index != self.current_file_index:
                self.load_file(index)


    def save_annotations(self):
        """Saves all annotations (entities and relations) for all loaded files to a JSON file."""
        # Check if there's anything worth saving
        if not self.annotations or all(not data.get('entities') and not data.get('relations') for data in self.annotations.values()):
            messagebox.showinfo("Info", "There are no annotations to save.")
            return

        # Suggest a save location and filename
        initial_dir = ""
        initial_file = "annotations.json"
        if self.files_list:
            try:
                # Use the directory of the first loaded text file
                first_file_dir = os.path.dirname(self.files_list[0])
                initial_dir = first_file_dir
                dir_name = os.path.basename(first_file_dir)
                if dir_name: # If it's not the root directory
                    initial_file = dir_name + "_annotations.json"
            except Exception as e:
                 print(f"Info: Could not determine initial directory/filename suggestion: {e}")


        save_path = filedialog.asksaveasfilename(
            initialdir=initial_dir,
            initialfile=initial_file,
            defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
            title="Save Annotations As"
        )

        if not save_path: # User cancelled
            self.status_var.set("Save cancelled.")
            return

        # Prepare data for serialization: use relative paths if possible
        serializable_annotations = {}
        base_dir = os.path.dirname(self.files_list[0]) if self.files_list else None

        for file_path, data in self.annotations.items():
            entities = data.get("entities", [])
            relations = data.get("relations", [])

            # Skip files with no annotations
            if not entities and not relations:
                continue

            # Determine the key for the JSON (relative path or filename)
            key = file_path
            try:
                # Check if the file_path is within the base_dir
                if base_dir and os.path.commonpath([file_path, base_dir]) == base_dir:
                    key = os.path.relpath(file_path, start=base_dir).replace('\\', '/') # Use forward slashes
                else:
                    # Fallback to just the filename if not in the same directory structure
                    key = os.path.basename(file_path)
            except ValueError: # Might happen on Windows if paths are on different drives
                 key = os.path.basename(file_path) # Fallback to filename
            except Exception as e:
                print(f"Warning: Error determining relative path for {file_path}, using basename. Error: {e}")
                key = os.path.basename(file_path)

            # Sort annotations for consistent output (optional but good practice)
            # Sort entities by position
            sorted_entities = sorted(entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0)))
            # Sort relations by type then head ID
            sorted_relations = sorted(relations, key=lambda r: (r.get('type', ''), r.get('head_id','')))

            serializable_annotations[key] = {
                "entities": sorted_entities,
                "relations": sorted_relations
            }

        # Write to JSON file
        try:
            with open(save_path, 'w', encoding='utf-8') as f:
                json.dump(serializable_annotations, f, indent=2, ensure_ascii=False)
            self.status_var.set(f"Annotations saved to '{os.path.basename(save_path)}'")
        except IOError as e:
            messagebox.showerror("Save Error", f"Could not write to file '{save_path}':\n{e}")
            self.status_var.set("Error saving annotations (IO Error).")
        except Exception as e: # Catch potential JSON serialization errors etc.
             messagebox.showerror("Save Error", f"Failed to save annotations due to an unexpected error:\n{str(e)}")
             self.status_var.set("Error saving annotations.")


    # --- Entity Annotation ---

    # Helper for checking span overlap based on numeric line/char indices
    def _spans_overlap_numeric(self, start1_line, start1_char, end1_line, end1_char,
                               start2_line, start2_char, end2_line, end2_char):
        """Checks if two spans, defined by line/char numbers, overlap."""
        # Convert to comparable tuples (line, char)
        span1_start = (start1_line, start1_char)
        span1_end = (end1_line, end1_char)
        span2_start = (start2_line, start2_char)
        span2_end = (end2_line, end2_char)

        # Ensure start <= end for each span for comparison logic
        if span1_start > span1_end: span1_start, span1_end = span1_end, span1_start
        if span2_start > span2_end: span2_start, span2_end = span2_end, span2_start

        # Check for non-overlap conditions
        # Span 1 ends before Span 2 starts OR Span 1 starts after Span 2 ends
        is_disjoint = (span1_end <= span2_start) or (span1_start >= span2_end)

        return not is_disjoint

    # Helper to check overlap against a list of existing entity dictionaries
    def _is_overlapping_in_list(self, start_line, start_char, end_line, end_char, existing_entities_list):
        """Checks if the given span overlaps with any entity in the provided list."""
        for ann in existing_entities_list:
            # Ensure the existing annotation has the necessary keys
            if not all(k in ann for k in ['start_line', 'start_char', 'end_line', 'end_char']):
                print(f"Warning: Skipping overlap check against entity {ann.get('id','N/A')} due to missing position keys.")
                continue

            if self._spans_overlap_numeric(
                start_line, start_char, end_line, end_char,
                ann['start_line'], ann['start_char'], ann['end_line'], ann['end_char']
            ):
                return True # Overlap found
        return False # No overlap found

    # Specific check against entities in the currently loaded file
    def _is_overlapping_current_file(self, start_line, start_char, end_line, end_char):
        """Checks if the given span overlaps with existing ENTITIES in the *currently loaded* file's data."""
        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        if not entities:
             return False # No existing entities to overlap with
        return self._is_overlapping_in_list(start_line, start_char, end_line, end_char, entities)


    def annotate_selection(self):
        """Annotates the selected text in the text_area as an entity."""
        if not self.current_file_path:
            messagebox.showinfo("Info", "Please load a file first.")
            return
        if not self.entity_tags:
             messagebox.showwarning("Warning", "No entity tags defined. Please manage entity tags first.")
             return

        try:
            # Get selection indices from the text area
            start_pos = self.text_area.index(tk.SEL_FIRST)
            end_pos = self.text_area.index(tk.SEL_LAST)
            selected_text = self.text_area.get(start_pos, end_pos)

            # Basic validation
            if not selected_text.strip(): # Ignore if only whitespace selected
                messagebox.showinfo("Info", "No text selected or selection is only whitespace.")
                return

            # Convert indices to numeric line/char
            start_line, start_char = map(int, start_pos.split('.'))
            end_line, end_char = map(int, end_pos.split('.'))

            # Get selected tag
            tag = self.selected_entity_tag.get()
            if not tag:
                messagebox.showwarning("Warning", "No entity tag selected.")
                return

            # Check for overlap with existing annotations in this file
            if self._is_overlapping_current_file(start_line, start_char, end_line, end_char):
                messagebox.showwarning("Overlap Detected", "The selected text overlaps with an existing entity.")
                return

            # Get or create the annotation data for the current file
            file_data = self.annotations.setdefault(self.current_file_path, {"entities": [], "relations": []})
            entities_list = file_data.setdefault("entities", [])

            # Create the new annotation dictionary
            entity_id = uuid.uuid4().hex # Generate unique ID
            annotation = {
                'id': entity_id,
                'start_line': start_line,
                'start_char': start_char,
                'end_line': end_line,
                'end_char': end_char,
                'text': selected_text,
                'tag': tag
            }

            # Add to internal data structure
            entities_list.append(annotation)

            # Apply visual tag in the text area
            # Ensure the tag is configured with a color first
            if tag not in self.text_area.tag_names():
                self._configure_text_tags()
            # Check again if configuration worked (might fail for odd reasons)
            if tag in self.text_area.tag_names():
                 self.text_area.tag_add(tag, start_pos, end_pos)
            else:
                 print(f"Warning: Could not apply unconfigured tag '{tag}' to text area.")

            # Update the entities list display
            self.update_entities_list()

            # Select the newly added entity in the list for user feedback
            # Need update_idletasks to ensure treeview is populated before selection attempt
            self.root.update_idletasks()
            try:
                if self.entities_tree.exists(entity_id):
                     self.entities_tree.selection_set(entity_id)
                     self.entities_tree.focus(entity_id)
                     self.entities_tree.see(entity_id)
                else:
                     print(f"Warning: Could not select new entity {entity_id} in tree.")
            except Exception as e:
                print(f"Error selecting newly added entity {entity_id} in tree: {e}")

            # Update status bar
            status_text = f"Annotated: '{selected_text[:30].replace(os.linesep, ' ')}...' as {tag}"
            self.status_var.set(status_text)
            self._update_button_states() # Update buttons (e.g., Remove might become enabled)

        except tk.TclError as e:
            # Handle specific TclError for no selection
            if "text doesn't contain selection" in str(e).lower():
                messagebox.showinfo("Info", "Please select text to annotate.")
            else:
                # Show other TclErrors
                messagebox.showerror("Annotation Error", f"A Tkinter error occurred:\n{e}")
        except Exception as e:
             # Catch any other unexpected errors during annotation
             messagebox.showerror("Annotation Error", f"An unexpected error occurred during annotation:\n{e}")


    def remove_entity_annotation(self):
        """Removes selected entities from the Entities list and any relations associated with them."""
        selected_iids = self.entities_tree.selection()
        if not selected_iids:
            messagebox.showinfo("Info", "Select one or more entities from the list to remove.")
            return

        if not self.current_file_path or self.current_file_path not in self.annotations:
            messagebox.showerror("Error", "Cannot remove entity: No file or annotations loaded.")
            return

        # Confirmation dialog
        confirm = messagebox.askyesno("Confirm Removal",
            f"Remove {len(selected_iids)} selected entities?\n\n"
            f"WARNING: This will also remove any relations involving these entities.")
        if not confirm:
            return

        file_data = self.annotations.get(self.current_file_path, {})
        entities = file_data.get("entities", [])
        relations = file_data.get("relations", [])

        removed_entity_count = 0
        relations_to_remove_ids = set() # Store IDs of relations to be removed
        entities_remaining = [] # Build a new list of entities to keep

        # Process entities
        for entity in entities:
            entity_id = entity.get('id')
            if not entity_id:
                entities_remaining.append(entity) # Keep entities without IDs? Or log error? Let's keep.
                continue

            if entity_id in selected_iids:
                removed_entity_count += 1
                # Remove corresponding highlight from text area
                try:
                    start_pos = f"{entity['start_line']}.{entity['start_char']}"
                    end_pos = f"{entity['end_line']}.{entity['end_char']}"
                    tag = entity.get('tag')
                    # Only remove if tag exists and text area is normal
                    if tag and tag in self.entity_tags and self.text_area.cget('state') == tk.NORMAL:
                         self.text_area.tag_remove(tag, start_pos, end_pos)
                except (tk.TclError, KeyError) as e:
                     print(f"Warning: Could not remove tag for removed entity {entity_id}: {e}")

                # Mark relations involving this entity for removal
                if relations:
                    for relation in relations:
                         relation_id = relation.get('id')
                         if not relation_id: continue
                         if relation.get('head_id') == entity_id or relation.get('tail_id') == entity_id:
                             relations_to_remove_ids.add(relation_id)
            else:
                # This entity was not selected for removal, keep it
                entities_remaining.append(entity)

        # Filter relations
        relations_remaining = []
        if relations:
            relations_remaining = [rel for rel in relations if rel.get('id') not in relations_to_remove_ids]
        removed_relation_count = (len(relations) if relations else 0) - len(relations_remaining)

        # Update the annotations data structure
        self.annotations[self.current_file_path]["entities"] = entities_remaining
        self.annotations[self.current_file_path]["relations"] = relations_remaining

        # Refresh UI
        self.update_entities_list()
        self.update_relations_list()
        # Re-apply highlights for remaining entities (simpler than selective removal sometimes)
        self.apply_annotations_to_text()

        self.status_var.set(f"Removed {removed_entity_count} entities and {removed_relation_count} associated relations.")
        self._update_button_states() # Update button states


    # <<< NEW METHOD for Merging >>>
    def merge_selected_entities(self):
        """Merges selected entities in the list to share the same ID."""
        selected_iids = self.entities_tree.selection()
        if len(selected_iids) < 2:
            messagebox.showinfo("Info", "Select two or more entities from the list to merge.")
            return

        if not self.current_file_path or self.current_file_path not in self.annotations:
            messagebox.showerror("Error", "Cannot merge entities: No file or annotations loaded.")
            return

        confirm = messagebox.askyesno(
            "Confirm Merge",
            f"Merge {len(selected_iids)} selected entities?\n\n"
            f"One ID will be chosen (the earliest occurring) and applied to all selected entities. "
            f"Any relations involving the other IDs will be updated to point to the chosen ID.\n\n"
            f"This action modifies the underlying annotation data."
        )
        if not confirm:
            self.status_var.set("Merge cancelled.")
            return

        file_data = self.annotations[self.current_file_path]
        entities = file_data.get("entities", [])
        relations = file_data.get("relations", [])

        # Find the actual entity dicts for selected iids and sort them by position
        selected_entities_data = []
        for iid in selected_iids:
            found = False
            for entity in entities:
                if entity.get('id') == iid:
                    try:
                        # Ensure position data exists for sorting
                        pos = (entity['start_line'], entity['start_char'])
                        selected_entities_data.append(entity)
                        found = True
                        break # Found the entity for this iid
                    except KeyError:
                         print(f"Warning: Skipping entity {iid} during merge - missing position data.")
            if not found:
                print(f"Warning: Selected entity ID {iid} not found in current file data.")
                # It's possible it was deleted between selection and clicking merge, although unlikely.
                # You could choose to abort here or continue with the ones found. Let's continue.

        if len(selected_entities_data) < 2:
             messagebox.showerror("Error", "Could not find at least two valid entities to merge from the selection.")
             return

        # Sort by start position (line, then char) to find the canonical one
        selected_entities_data.sort(key=lambda e: (e.get('start_line', 0), e.get('start_char', 0)))

        # The first entity in the sorted list provides the canonical ID
        canonical_entity = selected_entities_data[0]
        canonical_id = canonical_entity.get('id')
        if not canonical_id:
            messagebox.showerror("Error", "Failed to determine canonical ID for merging.")
            return

        # Create a set of IDs that need to be changed to the canonical ID
        ids_to_merge_away = {e.get('id') for e in selected_entities_data if e.get('id') != canonical_id and e.get('id')}

        if not ids_to_merge_away:
             messagebox.showinfo("Info", "Selected entities already share the same ID or only one valid entity found.")
             return

        modified_entity_count = 0
        modified_relation_count = 0

        # --- Perform the merge in the data structure ---

        # 1. Update Entity IDs
        # Iterate through the main entities list and update IDs in place
        for i, entity in enumerate(entities):
            if entity.get('id') in ids_to_merge_away:
                entities[i]['id'] = canonical_id
                modified_entity_count += 1 # Count how many entity records were changed

        # 2. Update Relation IDs
        if relations: # Only process if relations exist
            for i, rel in enumerate(relations):
                relation_modified_this_iter = False # Track if this specific relation was changed
                current_head_id = rel.get('head_id')
                current_tail_id = rel.get('tail_id')

                if current_head_id in ids_to_merge_away:
                    relations[i]['head_id'] = canonical_id
                    relation_modified_this_iter = True
                if current_tail_id in ids_to_merge_away:
                    relations[i]['tail_id'] = canonical_id
                    relation_modified_this_iter = True

                if relation_modified_this_iter:
                    modified_relation_count += 1 # Count changed relation *references*


        # 3. (Optional but recommended) Remove potentially duplicate relations created by the merge
        if relations and modified_relation_count > 0: # Only check if relations were potentially changed
            unique_relations = []
            seen_relations = set() # Store signatures (head_id, tail_id, type) of unique relations
            relations_before_dedup = len(relations)

            for rel in relations:
                # Create a tuple signature for the relation (ignoring the 'id' field)
                rel_sig = (rel.get('head_id'), rel.get('tail_id'), rel.get('type'))

                # Check for self-loops (optional: decide whether to keep or remove them)
                if rel.get('head_id') == rel.get('tail_id'):
                    print(f"Warning: Relation {rel.get('id')} became a self-loop after merge. Keeping it.")
                    # Alternatively, to remove self-loops:
                    # print(f"Info: Removing relation {rel.get('id')} as it became a self-loop after merge.")
                    # continue # Skip adding this self-loop relation to unique_relations

                # Check if this exact relation signature has been seen before
                if rel_sig not in seen_relations:
                    seen_relations.add(rel_sig)
                    unique_relations.append(rel) # Keep the first occurrence
                else:
                     # Log the removal of a duplicate
                     print(f"Info: Removing duplicate relation (Head: {rel.get('head_id')[:6]}..., Tail: {rel.get('tail_id')[:6]}..., Type: {rel.get('type')}) created by merge.")

            removed_duplicates = relations_before_dedup - len(unique_relations)
            if removed_duplicates > 0:
                 # Update the main relations list in the annotations
                 self.annotations[self.current_file_path]["relations"] = unique_relations
                 # Adjust the count for the status message (optional)
                 # modified_relation_count -= removed_duplicates # This might be confusing, maybe report separately


        # --- Update UI ---

        # 4. Refresh Treeviews
        self.update_entities_list() # This will re-render the list and apply the 'merged' tag visually
        self.update_relations_list() # This will show updated head/tail entity references

        # 5. Re-select the merged entities in the tree for visual feedback
        self.root.update_idletasks() # Allow tkinter to process UI updates
        try:
            # Clear previous selection first
            self.entities_tree.selection_set([])

            # Find all tree items that now have the canonical ID
            items_with_canonical_id = []
            for item_iid in self.entities_tree.get_children(""): # Iterate over top-level items
                 # Get the actual values associated with the tree item
                 item_values = self.entities_tree.item(item_iid, 'values')
                 # Check if the first value (which corresponds to the 'ID' column data) matches
                 if item_values and item_values[0] == canonical_id:
                     items_with_canonical_id.append(item_iid)

            if items_with_canonical_id:
                # Select all found items
                self.entities_tree.selection_set(items_with_canonical_id)
                # Focus and ensure the first one is visible
                self.entities_tree.focus(items_with_canonical_id[0])
                self.entities_tree.see(items_with_canonical_id[0])

        except Exception as e:
            print(f"Warning: Error re-selecting merged entities in tree: {e}")

        # 6. Update status bar
        status_msg = f"Merged {len(selected_iids)} entities to ID {canonical_id[:6]}.... Updated {modified_relation_count} relation references."
        if 'removed_duplicates' in locals() and removed_duplicates > 0:
            status_msg += f" Removed {removed_duplicates} duplicate relations."
        self.status_var.set(status_msg)

        # 7. Update button states (e.g., merge button might become disabled if only 1 is selected now)
        self._update_button_states()


    def apply_annotations_to_text(self):
        """Applies highlighting for all ENTITIES of the current file to the text area."""
        if not self.current_file_path:
             return

        original_state = self.text_area.cget('state')
        if original_state == tk.DISABLED:
            self.text_area.config(state=tk.NORMAL) # Enable to modify tags

        # Remove all existing entity tags first to handle potential changes/removals
        for tag in self.entity_tags:
            try:
                 self.text_area.tag_remove(tag, "1.0", tk.END)
            except tk.TclError:
                 pass # Ignore errors if tag doesn't exist

        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])

        # Sort entities by position to apply tags correctly (though overlap isn't allowed here)
        sorted_entities = sorted(entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0)))

        # Re-apply tags based on the current entity list
        for ann in sorted_entities:
            try:
                start_pos = f"{ann['start_line']}.{ann['start_char']}"
                end_pos = f"{ann['end_line']}.{ann['end_char']}"
                tag = ann.get('tag')

                if tag and tag in self.entity_tags:
                    # Ensure the tag is configured (might have been added dynamically)
                    if tag not in self.text_area.tag_names():
                        self._configure_text_tags() # Attempt to configure it

                    # Apply the tag if it's now configured
                    if tag in self.text_area.tag_names():
                         self.text_area.tag_add(tag, start_pos, end_pos)
                    else:
                        print(f"Warning: Entity {ann.get('id','N/A')} has valid but unconfigurable tag '{tag}'. Highlighting skipped.")
                elif tag:
                    # Log if an entity has a tag not in the known list
                    print(f"Warning: Entity {ann.get('id','N/A')} has unknown tag '{tag}'. Highlighting skipped.")

            except (tk.TclError, KeyError, ValueError) as e:
                 # Catch errors during tag application (e.g., invalid indices, missing keys)
                 print(f"Warning: Error applying tag for entity {ann.get('id','N/A')}: {e}")


        # Restore the original text area state
        self.text_area.config(state=original_state if self.current_file_path else tk.DISABLED)

    def update_entities_list(self):
        """Updates the Entities Treeview with entities for the current file."""
        try:
            # Preserve selection if possible (though merging might invalidate some selections)
            # current_selection = self.entities_tree.selection()
            self.entities_tree.delete(*self.entities_tree.get_children())
        except Exception:
            pass # Ignore if tree is empty

        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        if not entities:
             self.selected_entity_ids_for_relation = []
             self._update_button_states()
             return # Nothing to display

        # Sort entities primarily for consistent display order
        sorted_entities = sorted(entities, key=lambda a: (a.get('start_line', 0), a.get('start_char', 0)))

        # <<< NEW: Count ID occurrences to identify merged entities >>>
        entity_id_counts = {}
        for ann in sorted_entities:
            entity_id = ann.get('id')
            if entity_id:
                entity_id_counts[entity_id] = entity_id_counts.get(entity_id, 0) + 1

        # Populate the tree
        for ann in sorted_entities:
            entity_id = ann.get('id')
            if not entity_id:
                print(f"Warning: Skipping entity with missing ID in list update: {ann}")
                continue

            try:
                start_pos_str = f"{ann['start_line']}.{ann['start_char']}"
                end_pos_str = f"{ann['end_line']}.{ann['end_char']}"
                full_text = ann.get('text', '')
                # Shorten text for display, handle newlines
                display_text = full_text.replace(os.linesep, ' ').replace('\n', ' ').replace('\r', '')[:60]
                if len(full_text) > 60: display_text += "..."

                tag = ann.get('tag', 'N/A')

                # <<< NEW: Apply 'merged' tag if ID count > 1 >>>
                treeview_tags = () # Default: no special tags
                if entity_id_counts.get(entity_id, 0) > 1:
                    treeview_tags = ('merged',) # Apply the tag we configured

                # Insert item using the entity ID as the Treeview item ID (iid)
                # The 'values' tuple MUST match the order of the 'columns' definition,
                # including the hidden 'ID' column at index 0.
                self.entities_tree.insert(
                    "", tk.END, iid=entity_id, values=(
                        entity_id,       # Value for hidden "ID" column
                        start_pos_str,   # Value for "Start" column
                        end_pos_str,     # Value for "End" column
                        display_text,    # Value for "Text" column
                        tag              # Value for "Tag" column
                    ),
                    tags=treeview_tags # <<< Pass the tags here for styling
                )
            except (KeyError, Exception) as e:
                # Catch potential errors during item insertion
                print(f"Error adding entity {entity_id} to list: {e}")


        # Clear relation selection helpers and update buttons
        self.selected_entity_ids_for_relation = []
        self._update_button_states()

        # Optional: Try to restore selection if needed, but merging makes this tricky.
        # It might be better to re-select based on the canonical ID as done in merge_selected_entities.


    def on_entity_select(self, event):
        """Handles selection changes in the Entities Treeview."""
        selected_iids = self.entities_tree.selection()
        # Store the selected IDs (for relation creation or merging)
        self.selected_entity_ids_for_relation = list(selected_iids)

        # Highlight corresponding text spans in the text area
        if self.text_area.cget('state') == tk.NORMAL:
            # Remove previous text selection highlight
            self.text_area.tag_remove(tk.SEL, "1.0", tk.END)

            entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
            first_entity_pos = None # To scroll to the first selected entity

            for iid in selected_iids:
                 # Find the entity data corresponding to the selected iid
                 for entity in entities:
                     if entity.get('id') == iid:
                         try:
                             start_pos = f"{entity['start_line']}.{entity['start_char']}"
                             end_pos = f"{entity['end_line']}.{entity['end_char']}"
                             # Apply the selection tag (tk.SEL)
                             self.text_area.tag_add(tk.SEL, start_pos, end_pos)
                             # Store the position of the first entity found to scroll to it
                             if first_entity_pos is None:
                                 first_entity_pos = start_pos
                         except (tk.TclError, KeyError, ValueError) as e:
                             print(f"Warning: Error highlighting entity {iid}: {e}")
                         break # Found the entity for this iid, move to next iid

            # Scroll the text area to make the first selected entity visible
            if first_entity_pos:
                try:
                    self.text_area.see(first_entity_pos)
                except tk.TclError as e:
                     print(f"Warning: Error scrolling to entity: {e}")

        # Update button states based on the new selection count
        self._update_button_states()


    # --- Relation Annotation ---
    def add_relation(self):
        """Adds a relation between the two selected entities (Head -> Tail)."""
        if len(self.selected_entity_ids_for_relation) != 2:
            messagebox.showerror("Selection Error", "Select exactly TWO entities from the list (Head first, then Tail).")
            return

        # Assume the first selected is Head, second is Tail based on selection order in Treeview
        # Note: Treeview selection order isn't guaranteed across platforms/versions,
        # but it's the common assumption here. A more robust UI might have separate Head/Tail selectors.
        head_id = self.selected_entity_ids_for_relation[0]
        tail_id = self.selected_entity_ids_for_relation[1]

        relation_type = self.selected_relation_type.get()
        if not relation_type:
            messagebox.showerror("Selection Error", "Select a relation type.")
            return

        if not self.current_file_path or self.current_file_path not in self.annotations:
            messagebox.showerror("Error", "Cannot add relation: No file/annotations loaded.")
            return

        file_data = self.annotations.setdefault(self.current_file_path, {"entities": [], "relations": []})
        relations_list = file_data.setdefault("relations", [])

        # Check for duplicates before adding
        for rel in relations_list:
             if rel.get('head_id') == head_id and rel.get('tail_id') == tail_id and rel.get('type') == relation_type:
                 messagebox.showwarning("Duplicate Relation", "This exact relation (Head->Tail, Type) already exists.")
                 return
             # Optional: Check for inverse relation if symmetric relations are disallowed
             # if relation_type in symmetric_types and rel.get('head_id') == tail_id and rel.get('tail_id') == head_id and rel.get('type') == relation_type:
             #     messagebox.showwarning("Duplicate Relation", "The inverse of this symmetric relation already exists.")
             #     return

        # Generate unique ID for the relation
        relation_id = uuid.uuid4().hex
        new_relation = {
            "id": relation_id,
            "type": relation_type,
            "head_id": head_id,
            "tail_id": tail_id
        }

        # Add to data structure
        relations_list.append(new_relation)

        # Update UI list
        self.update_relations_list()

        # Select the new relation in the list
        self.root.update_idletasks() # Ensure tree is updated
        try:
            if self.relations_tree.exists(relation_id):
                 self.relations_tree.selection_set(relation_id)
                 self.relations_tree.focus(relation_id)
                 self.relations_tree.see(relation_id)
            else:
                 print(f"Warning: New relation '{relation_id}' not found in tree after update.")
        except Exception as e:
             print(f"Error selecting new relation in tree: {e}")

        self.status_var.set(f"Added Relation: {relation_type} ({head_id[:4]}... -> {tail_id[:4]}...)")
        # No button state change expected just from adding a relation


    # <<< NEW METHOD >>>
    def flip_selected_relation(self):
        """Flips the Head and Tail entities for the selected relation."""
        selected_iids = self.relations_tree.selection()
        if len(selected_iids) != 1:
            # This check is technically redundant due to button state, but good practice
            messagebox.showerror("Selection Error", "Please select exactly ONE relation from the list to flip.")
            return

        relation_id_to_flip = selected_iids[0]

        # Check if file and relations data are loaded
        if not self.current_file_path or \
           not self.annotations.get(self.current_file_path, {}).get("relations"):
            messagebox.showerror("Error", "Cannot flip relation: No file or relation data loaded.")
            return

        relations = self.annotations[self.current_file_path]["relations"]
        found = False
        for i, rel in enumerate(relations):
            if rel.get('id') == relation_id_to_flip:
                # Found the relation, perform the flip in place
                current_head = rel.get('head_id')
                current_tail = rel.get('tail_id')
                if current_head and current_tail: # Ensure both IDs exist
                    # Swap the values in the data structure
                    relations[i]['head_id'] = current_tail
                    relations[i]['tail_id'] = current_head
                    found = True
                    break # Exit loop once found and flipped
                else:
                    messagebox.showerror("Data Error", "Selected relation is missing Head or Tail ID.")
                    return # Don't proceed if data is corrupt

        if found:
            # Update the UI list display
            self.update_relations_list()
            # Re-select the flipped relation for visual confirmation
            self.root.update_idletasks()
            try:
                if self.relations_tree.exists(relation_id_to_flip):
                     self.relations_tree.selection_set(relation_id_to_flip)
                     self.relations_tree.focus(relation_id_to_flip)
                     self.relations_tree.see(relation_id_to_flip)
            except Exception as e:
                print(f"Warning: Error re-selecting flipped relation {relation_id_to_flip}: {e}")

            # Update status bar
            self.status_var.set("Relation Head/Tail flipped.")
        else:
            # Should be rare if button state is correct
            messagebox.showwarning("Not Found", "Could not find the selected relation in the internal data.")

        # Button states are updated by update_relations_list() -> _update_button_states()


    def remove_relation_annotation(self):
        """Removes the selected relation from the Relations list."""
        selected_iids = self.relations_tree.selection()
        # Button state logic should ensure only one is selected when this is called
        if not selected_iids: # Safety check
            messagebox.showinfo("Info", "Select a relation to remove.")
            return

        relation_id_to_remove = selected_iids[0]

        # Verify data exists
        if not self.current_file_path or \
           not self.annotations.get(self.current_file_path, {}).get("relations"):
            messagebox.showerror("Error", "Cannot remove relation: No file/annotations loaded.")
            return

        relations = self.annotations[self.current_file_path]["relations"]
        removed = False
        new_relations_list = [] # Build a new list excluding the one to remove

        for rel in relations:
            if rel.get('id') == relation_id_to_remove:
                removed = True
                # Don't append this one to the new list
            else:
                new_relations_list.append(rel)

        if removed:
            # Update the data structure with the filtered list
            self.annotations[self.current_file_path]["relations"] = new_relations_list
            # Update the UI list
            self.update_relations_list()
            self.status_var.set("Relation removed.")
        else:
             # Should be rare if selection/button state is correct
             messagebox.showwarning("Not Found", "Could not find the selected relation to remove.")

        # Button states are updated by update_relations_list() -> _update_button_states()


    def update_relations_list(self):
        """Updates the Relations Treeview with relations for the current file."""
        try:
            self.relations_tree.delete(*self.relations_tree.get_children())
        except Exception:
            pass # Ignore if tree empty

        # Get current data safely
        entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        relations = self.annotations.get(self.current_file_path, {}).get("relations", [])

        if not relations:
            # No relations to display, ensure buttons are updated based on entity selection
            self._update_button_states()
            return

        # Create a quick lookup map from entity ID to its display text
        entity_text_map = {}
        if entities:
            for entity in entities:
                eid = entity.get('id')
                etext = entity.get('text', 'N/A')
                if eid:
                    # Prepare a shortened, single-line version for the relation list
                    display_text = etext.replace(os.linesep, ' ').replace('\n',' ').replace('\r','')[:30]
                    if len(etext) > 30: display_text += "..."
                    # Store the display text, potentially adding tag info
                    # display_text += f" [{entity.get('tag','?')}]" # Optional: add tag
                    entity_text_map[eid] = display_text

        items_added = 0
        # Sort relations before display (optional)
        sorted_relations = sorted(relations, key=lambda r: (r.get('type', ''), r.get('head_id','')))

        for rel in sorted_relations:
            rel_id = rel.get('id')
            head_id = rel.get('head_id')
            tail_id = rel.get('tail_id')
            rel_type = rel.get('type')

            # Basic validation of the relation data
            if not (rel_id and head_id and tail_id and rel_type):
                print(f"Warning: Skipping invalid relation data in list update: {rel}")
                continue

            # Get display text for head and tail using the map
            # Fallback to showing partial ID if entity not found (e.g., after deletion/merge error)
            head_text = entity_text_map.get(head_id, f"<ID: {head_id[:6]}...>")
            tail_text = entity_text_map.get(tail_id, f"<ID: {tail_id[:6]}...>")

            # Prepare values tuple for treeview insertion (must match 'columns' definition)
            # (Hidden ID, Displayed Head, Displayed Type, Displayed Tail)
            values_to_insert = (rel_id, head_text, rel_type, tail_text)

            try:
                self.relations_tree.insert("", tk.END, iid=rel_id, values=values_to_insert)
                items_added += 1
            except Exception as e:
                print(f"Error inserting relation {rel_id} into tree: {e}")

        # Update button states after potentially changing the relation list
        self._update_button_states()


    def on_relation_select(self, event):
        """Handles selection changes in the Relations Treeview."""
        # The main purpose is to update button states (Flip/Remove depend on single selection)
        self._update_button_states()


    # --- Propagation (From Current File) ---
    def propagate_annotations(self):
        """Propagate ENTITY annotations from the *current* file to ALL files."""
        if not self.current_file_path or not self.files_list:
            messagebox.showinfo("Info", "Load a directory first.")
            return

        source_entities = self.annotations.get(self.current_file_path, {}).get("entities", [])
        if not source_entities:
            messagebox.showinfo("Info", "No entities in the current file to propagate.")
            return

        # Create a dictionary of {text: tag} from the source entities
        # Ignore entities with empty text or no tag
        text_to_tag = {
            ann['text']: ann['tag'] for ann in source_entities
            if ann.get('text','').strip() and ann.get('tag')
        }

        if not text_to_tag:
            messagebox.showinfo("Info", "No valid entity text/tag pairs found in the current file to propagate.")
            return

        confirm = messagebox.askyesno("Confirm Propagation (Current File)",
            f"Search for text from entities in '{os.path.basename(self.current_file_path)}' "
            f"across all {len(self.files_list)} files and apply tags?\n\n"
            f"({len(text_to_tag)} unique text/tag pairs found).\n\n"
            f"WARNING: This will add new annotations. Overlapping annotations will be skipped. "
            f"Relations are NOT propagated."
        )
        if not confirm:
            self.status_var.set("Propagation cancelled.")
            return

        # Call the common propagation logic
        self._perform_propagation(text_to_tag, "Current File Propagation")


    # --- Dictionary Propagation ---
    def load_and_propagate_from_dictionary(self):
        """Loads a dictionary file and propagates entities based on it."""
        if not self.files_list:
            messagebox.showerror("Error", "Open a directory first.")
            return

        if not self.entity_tags:
            messagebox.showwarning("Warning", "No entity tags defined in Settings. Add tags before using dictionary propagation.")
            return

        dict_path = filedialog.askopenfilename(
            title="Select Dictionary File (TSV/TXT/Space-separated)",
            filetypes=[("Text files", "*.txt"), ("TSV files", "*.tsv"), ("All files", "*.*")]
        )
        if not dict_path:
            self.status_var.set("Dictionary loading cancelled.")
            return

        # Read the dictionary file
        dictionary_mapping = {} # {text: tag}
        lines_read, valid_entries, skipped_lines = 0, 0, 0
        invalid_tags_found = set()
        try:
            with open(dict_path, 'r', encoding='utf-8') as f:
                for line_num, line in enumerate(f, 1):
                    lines_read += 1
                    line = line.strip()
                    if not line or line.startswith('#'): # Skip empty lines and comments
                         skipped_lines +=1; continue

                    # Try splitting by Tab first
                    parts = line.split('\t')
                    if len(parts) != 2:
                        # If not 2 parts by Tab, try splitting by the LAST space
                        # This handles multi-word entities like "New York City   Location"
                        parts = line.rsplit(maxsplit=1) # Split only on the last whitespace block

                    if len(parts) != 2:
                        print(f"Warning: Skipping malformed dictionary line {line_num}: '{line}' (Expected 'Entity Text<TAB/SPACE>Tag')")
                        skipped_lines += 1; continue

                    entity_text, label = parts[0].strip(), parts[1].strip()

                    if not entity_text: # Skip if entity text is empty after stripping
                        print(f"Warning: Skipping dictionary line {line_num} (empty entity text)")
                        skipped_lines += 1; continue

                    # Check if the label is a valid, currently defined entity tag
                    if label in self.entity_tags:
                        # Add to dictionary (overwrite if text appears multiple times)
                        if entity_text in dictionary_mapping and dictionary_mapping[entity_text] != label:
                             print(f"Warning: Dictionary line {line_num}: Text '{entity_text}' redefined from '{dictionary_mapping[entity_text]}' to '{label}'. Using last definition.")
                        dictionary_mapping[entity_text] = label
                        valid_entries += 1
                    else:
                        # Tag is not in the current list of entity tags
                        invalid_tags_found.add(label)
                        # Don't increment valid_entries, but count as skipped
                        skipped_lines += 1

        except Exception as e:
            messagebox.showerror("Dictionary Read Error", f"Failed to read dictionary file '{os.path.basename(dict_path)}':\n{e}")
            return

        # Report results of dictionary parsing
        if not dictionary_mapping:
            msg = f"Finished reading dictionary '{os.path.basename(dict_path)}'.\n"
            msg += f"Read {lines_read} lines. Found 0 valid entries.\n"
            if invalid_tags_found:
                 msg += f"Skipped lines due to unrecognized tags (e.g., {', '.join(list(invalid_tags_found)[:5])}{'...' if len(invalid_tags_found)>5 else ''}). "
                 msg += f"Ensure these tags exist in 'Settings -> Manage Entity Tags'.\n"
            if skipped_lines > len(invalid_tags_found):
                 msg += f"Other lines skipped due to formatting issues or empty text."
            messagebox.showinfo("Dictionary Parsing Results", msg)
            return

        # Confirm propagation with summary
        confirm_msg = f"Dictionary '{os.path.basename(dict_path)}' loaded.\n"
        confirm_msg += f"- Read {lines_read} lines.\n"
        confirm_msg += f"- Found {valid_entries} entries with valid tags.\n"
        confirm_msg += f"- Skipped {skipped_lines} lines "
        skipped_reasons = []
        if invalid_tags_found: skipped_reasons.append("unrecognized tags")
        if skipped_lines > len(invalid_tags_found): skipped_reasons.append("formatting/empty text")
        if skipped_reasons: confirm_msg += f"({', '.join(skipped_reasons)})"
        confirm_msg += ".\n"

        if invalid_tags_found:
             confirm_msg += f"- Example skipped tags: {', '.join(list(invalid_tags_found)[:5])}{'...' if len(invalid_tags_found)>5 else ''}\n"
             confirm_msg += f"  (Ensure these exist in Settings -> Manage Entity Tags)\n"

        confirm_msg += f"\nPropagate these {valid_entries} annotations across all {len(self.files_list)} files?\n\n"
        confirm_msg += f"(Existing annotations will NOT be overwritten. Overlaps will be skipped. Relations are not affected.)"

        confirm = messagebox.askyesno("Confirm Dictionary Propagation", confirm_msg)
        if not confirm:
            self.status_var.set("Dictionary propagation cancelled.")
            return

        # Call the common propagation logic
        self._perform_propagation(dictionary_mapping, "Dictionary Propagation")

    # --- COMMON Propagation Logic ---
    def _perform_propagation(self, text_to_tag_map, source_description):
        """Performs entity propagation across all files based on a text->tag map."""
        propagated_count = 0 # Total new annotations added across all files
        affected_files_count = 0 # Number of files that had at least one annotation added
        extend_option = self.extend_to_word.get() # Checkbox state
        current_file_was_modified = False # Track if the currently viewed file needs UI refresh

        self.status_var.set(f"Starting {source_description}...")
        self.root.update_idletasks() # Show status update immediately

        # Sort keys by length descending - match longest entities first
        # This helps prevent partial matches (e.g., matching "York" inside "New York")
        sorted_texts_to_find = sorted(text_to_tag_map.keys(), key=len, reverse=True)

        # Iterate through each file in the loaded list
        for i, file_path in enumerate(self.files_list):
            file_modified_in_this_run = False
            # Update status periodically
            if (i + 1) % 10 == 0 or i == len(self.files_list) - 1:
                self.status_var.set(f"{source_description}: Processing file {i+1}/{len(self.files_list)}...")
                self.root.update_idletasks()

            try:
                # Read file content
                with open(file_path, 'r', encoding='utf-8') as f:
                     content = f.read()
                # Use splitlines to handle different line endings gracefully
                lines = content.splitlines()

                # Get existing annotations for this file (or initialize if none)
                file_data = self.annotations.setdefault(file_path, {"entities": [], "relations": []})
                target_entities_list = file_data.setdefault("entities", [])

                # Iterate through the texts to find from the map (longest first)
                for text_to_find in sorted_texts_to_find:
                    tag_to_apply = text_to_tag_map[text_to_find]
                    if len(text_to_find) < 1: continue # Skip empty strings

                    # Search line by line
                    for line_num, line in enumerate(lines, 1): # Use 1-based line numbers for tk.Text
                        start_char_search = 0 # Start search from beginning of line
                        while True:
                            # Find the next occurrence of the text in the current line
                            found_char_index = line.find(text_to_find, start_char_search)
                            if found_char_index == -1:
                                break # Not found in the rest of this line

                            # Calculate initial match boundaries (0-based for string indexing)
                            match_start_char = found_char_index
                            match_end_char = found_char_index + len(text_to_find)
                            annotated_text = text_to_find # Text to store in annotation

                            # --- Optional: Extend to word boundaries ---
                            if extend_option:
                                word_start_char, word_end_char = match_start_char, match_end_char
                                # Extend backward if preceded by alphanumeric
                                while word_start_char > 0 and line[word_start_char - 1].isalnum():
                                     word_start_char -= 1
                                # Extend forward if followed by alphanumeric
                                while word_end_char < len(line) and line[word_end_char].isalnum():
                                     word_end_char += 1

                                # If extension occurred, update boundaries and text
                                if word_start_char != match_start_char or word_end_char != match_end_char:
                                     match_start_char = word_start_char
                                     match_end_char = word_end_char
                                     annotated_text = line[match_start_char:match_end_char]


                            # --- Check for Overlap ---
                            # Check against entities already present OR added *during this propagation run* for this file
                            # Use the potentially extended boundaries for the check
                            overlap = self._is_overlapping_in_list(
                                line_num, match_start_char, line_num, match_end_char,
                                target_entities_list # Check against the current state of this file's entities
                            )

                            # --- Add Annotation if No Overlap ---
                            if not overlap:
                                entity_id = uuid.uuid4().hex
                                new_annotation = {
                                    'id': entity_id,
                                    'start_line': line_num,
                                    'start_char': match_start_char,
                                    'end_line': line_num, # Single line match for now
                                    'end_char': match_end_char,
                                    'text': annotated_text, # Use potentially extended text
                                    'tag': tag_to_apply
                                }
                                target_entities_list.append(new_annotation) # Add to this file's data
                                propagated_count += 1 # Increment total count
                                file_modified_in_this_run = True # Mark this file as changed

                                # Check if the modified file is the one currently displayed
                                if file_path == self.current_file_path:
                                    current_file_was_modified = True

                            # --- Advance Search Position ---
                            # Move search start past the end of the current match to avoid re-matching overlaps immediately
                            start_char_search = match_end_char
                            # Safety break if search doesn't advance (e.g., finding empty string - though skipped earlier)
                            if start_char_search <= found_char_index:
                                 start_char_search = found_char_index + 1


                # After checking all texts for this file
                if file_modified_in_this_run:
                    affected_files_count += 1

            except Exception as e:
                 # Log errors encountered during processing a specific file
                 print(f"ERROR processing file '{os.path.basename(file_path)}' during propagation:\n{str(e)}")
                 # Optionally: messagebox.showerror(...) but might be too many popups

        # --- Post-Propagation Updates ---

        # If the currently viewed file was changed, update its UI elements
        if current_file_was_modified:
            self.update_entities_list() # Refresh entity list (will show new merged tags if any)
            self.apply_annotations_to_text() # Re-apply all highlights including new ones

        self._update_button_states() # Always update states after propagation run

        # Show summary message box
        summary = f"{source_description} complete.\n"
        summary += f"Added {propagated_count} new entities across {affected_files_count} files."
        if extend_option: summary += "\n('Extend to whole word' was enabled)"
        messagebox.showinfo("Propagation Results", summary)
        self.status_var.set(f"{source_description} finished. Added {propagated_count} entities.")


    # --- Tag/Type Management ---
    def _manage_items(self, item_type_name, current_items_list, update_combobox_func):
        """Generic function to open a modal window for managing a list of items (tags/types)."""
        # Create a Toplevel window (modal dialog)
        window = tk.Toplevel(self.root)
        window.title(f"Manage {item_type_name}")
        window.geometry("350x400"); window.resizable(False, False)
        window.transient(self.root); # Keep window on top of main app
        window.grab_set() # Make window modal (block interaction with main app)

        # Frame for the listbox and scrollbar
        list_frame = tk.Frame(window)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(10, 0))
        tk.Label(list_frame, text=f"Current {item_type_name}:").pack(anchor=tk.W)
        scrollbar = tk.Scrollbar(list_frame); scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        # Create a temporary list from the current items
        temp_items = list(current_items_list) # Copy the list

        # Listbox to display items
        listbox = tk.Listbox(list_frame, yscrollcommand=scrollbar.set, exportselection=False)
        for item in temp_items:
            listbox.insert(tk.END, item)
            # Special handling for entity tags to show color
            if item_type_name == "Entity Tags":
                color = self.get_color_for_tag(item)
                try:
                    listbox.itemconfig(tk.END, {'bg': color})
                except tk.TclError:
                    pass # Ignore color setting errors
        listbox.pack(fill=tk.BOTH, expand=True)
        scrollbar.config(command=listbox.yview)

        # Frame for Add/Remove controls
        controls_frame = tk.Frame(window)
        controls_frame.pack(fill=tk.X, padx=10, pady=10)

        item_var = tk.StringVar() # Variable for the entry field
        item_entry = tk.Entry(controls_frame, textvariable=item_var, width=20)
        item_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 5))

        def add_item():
            item = item_var.get().strip() # Get and clean input
            if item: # Only add if not empty
                # Check for duplicates (case-insensitive)
                existing_lower = [listbox.get(i).lower() for i in range(listbox.size())]
                if item.lower() not in existing_lower:
                    listbox.insert(tk.END, item)
                    # Apply color if it's an entity tag
                    if item_type_name == "Entity Tags":
                         color = self.get_color_for_tag(item)
                         try: listbox.itemconfig(tk.END, {'bg': color})
                         except tk.TclError: pass
                    item_var.set("") # Clear entry field
                    listbox.see(tk.END) # Scroll to the new item
                else:
                    messagebox.showwarning("Duplicate", f"'{item}' already exists (case-insensitive).", parent=window)
            item_entry.focus_set() # Keep focus on entry

        item_entry.bind("<Return>", lambda event: add_item()) # Add on Enter key

        add_btn = tk.Button(controls_frame, text="Add", width=7, command=add_item)
        add_btn.pack(side=tk.LEFT, padx=5)

        def remove_item():
            indices = listbox.curselection() # Get selected item indices
            if indices:
                # Iterate in reverse to avoid index shifting issues
                for index in reversed(indices):
                    listbox.delete(index)
            else:
                messagebox.showwarning("No Selection", "Select an item to remove.", parent=window)

        remove_btn = tk.Button(controls_frame, text="Remove", width=7, command=remove_item)
        remove_btn.pack(side=tk.LEFT)

        # Frame for Save/Cancel buttons
        button_frame = tk.Frame(window)
        button_frame.pack(fill=tk.X, padx=10, pady=(0, 10))

        def save_changes():
            new_items = list(listbox.get(0, tk.END)) # Get updated list from listbox
            # Basic validation: ensure at least one item remains (adjust if needed)
            if not new_items:
                 warning_msg = f"Cannot remove all {item_type_name}. At least one must remain."
                 if item_type_name == "Entity Tags": warning_msg += "\nAnnotations using removed tags will lose highlighting."
                 messagebox.showwarning("Warning", warning_msg, parent=window)
                 return # Don't save if list is empty

            # Check if changes were actually made
            if new_items != current_items_list:
                # --- Apply Changes ---
                # 1. Update the main application's list IN PLACE
                current_items_list[:] = new_items

                # 2. Update the corresponding Combobox
                update_combobox_func()

                # 3. Perform additional updates if needed (e.g., for Entity Tags)
                if item_type_name == "Entity Tags":
                    # Reconfigure text area tags with potentially new colors/tags
                    self._configure_text_tags()
                    # Re-apply highlights in the text area based on the updated tags
                    self.apply_annotations_to_text()
                    # Re-render entity list (tag column might change)
                    self.update_entities_list()

                self.status_var.set(f"{item_type_name} updated.")
            else:
                self.status_var.set(f"No changes made to {item_type_name}.")

            window.destroy() # Close the dialog

        save_btn = tk.Button(button_frame, text="Save Changes", width=12, command=save_changes)
        save_btn.pack(side=tk.RIGHT, padx=5)

        cancel_btn = tk.Button(button_frame, text="Cancel", width=12, command=window.destroy)
        cancel_btn.pack(side=tk.RIGHT)

        item_entry.focus_set() # Set initial focus to the entry field
        window.wait_window() # Wait for the dialog to be closed

    def manage_entity_tags(self):
        """Opens the modal window to manage entity tags."""
        self._manage_items("Entity Tags", self.entity_tags, self._update_entity_tag_combobox)

    def manage_relation_types(self):
        """Opens the modal window to manage relation types."""
        self._manage_items("Relation Types", self.relation_types, self._update_relation_type_combobox)

# --- Main Execution ---
def main():
    root = tk.Tk()
    style = ttk.Style()
    style.theme_use('default') # or 'alt', 'default', 'classic'
    app = TextAnnotator(root)
    root.mainloop()

if __name__ == "__main__":
    main()
