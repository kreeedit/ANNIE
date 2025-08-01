# ANNIE User Guide and Software Documentation

## Overview

ANNIE (Annotation Interface for Named-entity & Information Extraction) is a Python-based desktop application designed for annotating text files with named entities and directed relations between them. Built using Tkinter, it provides a user-friendly interface for loading text files, annotating text spans with customizable tags, defining relations, and exporting annotations for machine learning tasks. Key features include:

- **Entity Annotation**: Tag text spans as entities (e.g., Person, Organization) with customizable tags and colors.
- **Relation Annotation**: Define directed relations between entities (e.g., "spouse_of", "works_at").
- **Propagation**: Propagate entity annotations across files manually or using a dictionary.
- **AI Pre-annotation**: Leverage a pre-trained NER model (optional, requires transformers and torch libraries).
- **Session Management**: Save and load annotation sessions.
- **Export/Import**: Support for CoNLL and spaCy JSONL formats.
- **Advanced Features**: Multi-label annotations, entity merging/demerging, relation flipping, and read-only text area.

This guide provides detailed instructions for using ANNIE and technical documentation for its implementation.

---

## System Requirements

- **Operating System**: Windows, macOS, or Linux.
- **Python**: Version 3.6 or higher.
- **Required Libraries**:
  - `tkinter` (included with Python).
  - `json`, `os`, `shutil`, `pathlib`, `uuid`, `itertools`, `re`, `time`, `threading` (standard Python libraries).
- **Optional Libraries** (for AI pre-annotation):
  - `transformers` and `torch` (install via `pip install transformers torch`).
- **Hardware**: No specific requirements beyond standard desktop capabilities. For AI pre-annotation, a CPU is sufficient (configurable via `AI_DEVICE = "cpu"`).

---

## Installation

1. **Install Python**: Ensure Python 3.6+ is installed. Download from [python.org](https://www.python.org).
2. **Install Required Libraries**:
   - Tkinter is included with Python.
   - For AI pre-annotation, install optional libraries:
     ```bash
     pip install transformers torch
     ```
3. **Download ANNIE**:
   - Save the provided Python script as `annie.py`.
4. **Run ANNIE**:
   - Execute the script:
     ```bash
     python annie.py
     ```
   - The application will launch with a modern Tkinter theme (e.g., 'clam', 'alt') if available.

---

## User Guide

### 1. Getting Started

1. **Launch ANNIE**:
   - Run `annie.py`. The main window opens with the title "ANNIE - Annotation Interface" and a default size of 1200x850 pixels.
2. **Interface Overview**:
   - **Left Panel**: File listbox and navigation buttons (Previous/Next).
   - **Right Panel**:
     - **Top**: Text area (read-only) for viewing and annotating text.
     - **Middle**: Controls for entity and relation annotation.
     - **Bottom**: Lists of entities and relations.
   - **Bottom**: Status bar for feedback.
   - **Menu Bar**: File and Settings menus for session management, schema configuration, and advanced features.

### 2. Loading Files

- **Open Directory**:
  - Go to `File > Open Directory`.
  - Select a directory containing `.txt` files.
  - ANNIE loads all `.txt` files in alphabetical order, displaying filenames in the left panel.
  - The first file loads automatically, and its content appears in the text area.
- **Add Files to Session**:
  - Use `File > Add File(s) to Session...` to copy additional `.txt` files into the session’s directory.
  - Files are added without duplicates, and the file list updates.
- **Navigate Files**:
  - Click a file in the listbox or use the Previous/Next buttons to switch files.
  - The status bar shows the current file and its position (e.g., "Loaded: example.txt (1/5)").

### 3. Entity Annotation

- **Select Text**:
  - Drag to highlight text in the read-only text area or double-click to select a word.
  - Use the "Extend to word" checkbox to snap selections to word boundaries.
- **Choose a Tag**:
  - Select a tag (e.g., Person, Organization) from the Entity Tag dropdown.
  - Use hotkeys (0-9) to quickly set the current tag (e.g., press `1` for the first tag).
- **Annotate**:
  - Click "Annotate Sel" to tag the selected text.
  - Annotations appear in the text area with colored backgrounds (e.g., Person: #ffcccc) and in the Entities list.
  - Propagated entities (from AI or dictionary) are underlined.
- **Remove Annotations**:
  - Single-click an annotated span to prompt for removal.
  - Select entities in the Entities list and click "Remove Sel" or press `Delete`.
- **Multi-label Annotations**:
  - Enable "Allow Multi-label & Overlapping Annotations" in the Settings menu to allow overlapping tags.
  - Without this, overlapping annotations are blocked.
- **Hotkey Relabeling**:
  - Select entities in the Entities list and press a number key (0-9) to relabel them with the corresponding tag.

### 4. Relation Annotation

- **Select Entities**:
  - In the Entities list, select exactly two entities (Ctrl+click for multiple selections).
  - Selected entities are highlighted in the text area with a black border.
- **Choose a Relation Type**:
  - Select a type (e.g., spouse_of) from the Relation Type dropdown.
- **Add Relation**:
  - Click "Add Relation (Head->Tail)" to create a directed relation from the first to the second selected entity.
  - The relation appears in the Relations list.
- **Flip Relation**:
  - Select a relation and click "Flip H/T" to swap head and tail entities.
- **Remove Relation**:
  - Select a relation and click "Remove Relation" or press `Delete`.

### 5. Entity Merging and Demerging

- **Merge Entities**:
  - Select multiple entity instances in the Entities list.
  - Click "Merge Sel." to assign them the same ID, treating them as the same entity.
  - Merged entities appear in grey italics in the Entities list.
- **Demerge Entities**:
  - Right-click an annotated span in the text area.
  - If the entity has multiple instances, select "Demerge This Instance" to assign it a new unique ID.

### 6. Propagation

- **Propagate Entities**:
  - Click "Propagate Entities" to copy entities from the current file to all files, matching exact text and tag.
  - Confirm the action in the dialog.
- **Dictionary-Based Propagation**:
  - Go to `Settings > Load Dictionary & Propagate Entities...`.
  - Select a `.txt` file with entries in the format `text tag` (e.g., `John Person`).
  - Entities are propagated across all files, respecting word boundaries.
- **Overlap Handling**:
  - Propagation respects the "Allow Multi-label & Overlapping Annotations" setting.
  - Propagated entities are underlined in the text area.

### 7. AI Pre-annotation

- **Requirements**: Install `transformers` and `torch` libraries.
- **Run AI**:
  - Press `a` or go to `Settings > Pre-annotate with AI...`.
  - ANNIE uses the `Babelscape/wikineural-multilingual-ner` model to annotate Person, Organization, and Location entities in the current file.
  - Annotations are added as propagated (underlined) and respect overlap settings.
- **Progress**: The status bar shows chunk processing (e.g., "Annotating chunk 1/3...").
- **Limitations**: Requires a loaded file with content. Fails gracefully if libraries are missing.

### 8. Session Management

- **Save Session**:
  - Go to `File > Save Session` or `Save Session As...`.
  - Saves files list, annotations, tags, and settings to a `.json` file.
- **Load Session**:
  - Go to `File > Load Session...`.
  - Loads a previously saved session, checking for missing files.
- **Exit Confirmation**:
  - On closing, ANNIE prompts to save unsaved changes.

### 9. Import/Export Annotations

- **Export Annotations**:
  - Go to `File > Export for Training...`.
  - Choose `.conll` (CoNLL-2003 format) or `.jsonl` (spaCy JSONL format).
  - Exports entities for all files with annotations.
- **Import Annotations**:
  - Go to `File > Import Annotations...`.
  - Select a `.conll` or `.jsonl` file.
  - Choose a directory to save new `.txt` files.
  - New tags are prompted for addition to the schema.
  - Imported documents are added to the session.

### 10. Schema Management

- **Manage Tags/Types**:
  - Go to `Settings > Manage Entity Tags...` or `Manage Relation Types...`.
  - Add, remove, or reorder tags/types in a dialog.
  - Entity tags (up to 10) show hotkey numbers (0-9).
- **Save/Load Schema**:
  - Use `Settings > Save Tag/Relation Schema...` to save tags and types to a `.json` file.
  - Use `Settings > Load Tag/Relation Schema...` to replace current tags/types.

### 11. Keyboard Shortcuts

- **0-9**: Set current entity tag or relabel selected entities.
- **a**: Run AI pre-annotation.
- **Delete**: Remove selected entities or relations.
- **Arrow Keys**: Navigate lists (Entities/Relations).
- **Printable Characters**: Jump to entities/relations starting with the typed character.

---

## Technical Documentation

### Architecture

- **Language**: Python 3, using Tkinter for the GUI and optional `transformers` for AI.
- **Main Class**: `TextAnnotator`
  - Initializes the UI, manages state, and handles annotation logic.
  - Attributes:
    - `root`: Tkinter root window.
    - `annotations`: Dictionary mapping file paths to entities and relations.
    - `entity_tags`, `relation_types`: Lists of tags and relation types.
    - `tag_colors`: Dictionary mapping tags to background colors.
    - `files_list`, `current_file_path`: Manage loaded files.
- **File Format**: Text files (`.txt`) for input, JSON for sessions and schemas, CoNLL/JSONL for export/import.

### Key Methods

- **Initialization** (`__init__`):
  - Sets up the UI with a menu bar, file listbox, text area, control panel, and entity/relation lists.
  - Configures default tags, colors, and hotkeys.
- **File Handling**:
  - `load_directory`: Loads `.txt` files from a directory.
  - `add_files_to_session`: Copies files into the session directory.
  - `load_file`: Displays a file’s content and annotations.
- **Annotation**:
  - `annotate_selection`: Tags selected text with the chosen tag.
  - `_on_double_click`: Annotates a word on double-click.
  - `_on_highlight_release`: Handles click-to-remove and drag-to-annotate.
  - `add_relation`, `flip_selected_relation`, `remove_relation_annotation`: Manage relations.
- **Merging/Demerging**:
  - `merge_selected_entities`: Assigns the same ID to selected entities.
  - `demerge_entity`: Assigns a new ID to a specific entity instance.
- **Propagation**:
  - `propagate_annotations`: Copies entities across files.
  - `load_and_propagate_from_dictionary`: Uses a dictionary for propagation.
- **AI Pre-annotation**:
  - `pre_annotate_with_ai`: Runs NER in a thread using `transformers`.
  - `_run_ai_model`: Processes text in chunks with a sliding window.
- **Import/Export**:
  - `export_annotations`: Saves annotations in CoNLL or JSONL format.
  - `import_annotations`: Imports annotations and creates new files.
- **Session Management**:
  - `save_session`, `load_session`: Handle session persistence.
- **UI Updates**:
  - `apply_annotations_to_text`: Highlights annotations in the text area.
  - `update_entities_list`, `update_relations_list`: Refresh list views.

### Data Structures

- **Annotations**:
  ```json
  {
    "file_path": {
      "entities": [
        {
          "id": "uuid",
          "start_line": int,
          "start_char": int,
          "end_line": int,
          "end_char": int,
          "text": "string",
          "tag": "string",
          "propagated": bool
        }
      ],
      "relations": [
        {
          "id": "uuid",
          "type": "string",
          "head_id": "uuid",
          "tail_id": "uuid"
        }
      ]
    }
  }
  ```
- **Session File**:
  ```json
  {
    "version": "1.12",
    "files_list": ["path1", "path2"],
    "current_file_index": int,
    "entity_tags": ["Person", "Organization", ...],
    "relation_types": ["spouse_of", "works_at", ...],
    "tag_colors": {"Person": "#ffcccc", ...},
    "annotations": {...},
    "extend_to_word": bool,
    "allow_multilabel_overlap": bool
  }
  ```
- **Dictionary File** (for propagation):
  ```
  John Person
  Google Organization
  ```

### Implementation Notes

- **Read-Only Text Area**: Prevents accidental edits (`state=tk.DISABLED`).
- **Color Management**: Uses a cycle of pastel colors for new tags.
- **AI Pre-annotation**:
  - Uses `Babelscape/wikineural-multilingual-ner` with a sliding window (512 tokens, 128-token stride).
  - Runs in a separate thread to avoid freezing the UI.
- **Error Handling**: Gracefully handles missing files, invalid formats, and library absence.
- **Performance**: Efficiently processes large texts using regex for propagation and token-based chunking for AI.

---

## Troubleshooting

- **AI Pre-annotation Fails**:
  - Ensure `transformers` and `torch` are installed.
  - Check for sufficient memory if processing large files.
- **Missing Files on Session Load**:
  - ANNIE warns about missing files and allows continuing with available ones.
- **Overlap Issues**:
  - Enable "Allow Multi-label & Overlapping Annotations" in Settings if overlaps are desired.
- **UI Responsiveness**:
  - Large files may slow down; consider breaking them into smaller files.
- **Export Errors**:
  - Ensure write permissions in the save directory.
  - Verify file extensions (`.conll`, `.jsonl`).

---

## Future Improvements

- Add support for custom AI models.
- Implement undo/redo for annotations.
- Enhance export formats (e.g., BRAT, IOB).
- Add visualization for relations (e.g., arrows in text).
- Support batch processing for propagation and AI annotation.

---

This guide and documentation provide a comprehensive overview of ANNIE’s functionality and implementation. For further assistance, refer to the console output for detailed error messages or contact the developer.