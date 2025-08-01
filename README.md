# ANNIE - Annotation Interface for Named-entity & Information Extraction

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](https://opensource.org/licenses/Apache-2.0)

ANNIE is a lightweight, Python-based desktop application designed for annotating text files with named entities and directed relations. Built with Tkinter, it offers a user-friendly interface for researchers, linguists, and NLP practitioners to create high-quality annotated datasets for named entity recognition (NER) and relation extraction tasks.

<p align="center">
  <img src="annie.gif" width="400" />
</p>

## Features

- **Entity Annotation**: Tag text spans with customizable labels (e.g., Person, Organization, Location).
- **Relation Annotation**: Define directed relations between entities (e.g., "spouse_of", "works_at").
- **Batch Processing**: Load and annotate multiple `.txt` files from a directory.
- **Entity Propagation**: Automatically annotate matching text spans across all files, with optional dictionary-based propagation.
- **AI Pre-annotation**: Use a pre-trained NER model (requires `transformers` and `torch`) for automated entity tagging.
- **Entity Merging/Demerging**: Merge multiple mentions of the same entity or separate them via right-click.
- **Relation Flipping**: Reverse the direction of relations with a single click.
- **Multi-label & Overlapping Annotations**: Optionally allow multiple tags or overlapping annotations.
- **Session Management**: Save and load annotation sessions to resume work.
- **Export/Import**: Support for CoNLL-2003 and spaCy JSONL formats for training data.
- **Color-coded Visualization**: Highlight entities with tag-specific colors; propagated entities are underlined.
- **Read-only Text Area**: Prevents accidental modifications.
- **Hotkey Support**: Use keys 0-9 for quick tag selection/relabeling and `a` for AI pre-annotation.
- **Flexible Schema**: Customize entity tags and relation types, with save/load functionality.

## Getting Started

### Prerequisites

- **Python**: 3.6 or higher.
- **Required Libraries**: `tkinter` (included with Python), `json`, `os`, `shutil`, `pathlib`, `uuid`, `itertools`, `re`, `time`, `threading`.
- **Optional Libraries**: `transformers` and `torch` for AI pre-annotation (`pip install transformers torch`).

### Installation

1. Clone this repository or download the source code.
2. Navigate to the project directory.
3. Run the application:
   ```bash
   python annie.py
   ```

<p align="center">
  <img src="annie_app.png" width="800" />
</p>

## Basic Usage

### 1. Loading Files
1. Go to **File → Open Directory** and select a folder with `.txt` files.
2. Files load in alphabetical order; the first file displays automatically.
3. Use **Previous**/**Next** buttons or click a file in the listbox to navigate.
4. Add files to the session via **File → Add File(s) to Session...**.

### 2. Entity Annotation
1. Drag to select text or double-click a word in the text area.
2. Choose a tag from the Entity Tag dropdown or press 0-9 to select a tag.
3. Click **Annotate Sel** to tag the selection.
4. Entities appear in the Entities list and are highlighted with tag-specific colors.
5. Single-click an annotated span to remove it, or select entities and click **Remove Sel**.
6. Enable **Extend to word** to snap selections to word boundaries.
7. Relabel entities by selecting them and pressing 0-9.

### 3. Relation Annotation
1. Select exactly two entities in the Entities list (first = head, second = tail).
2. Choose a relation type from the Relation Type dropdown.
3. Click **Add Relation (Head→Tail)** to create the relation.
4. Relations appear in the Relations list.
5. Select a relation and click **Flip H/T** to reverse it or **Remove Relation** to delete it.

### 4. Saving Annotations
- Go to **File → Save Annotations** to export annotations as a JSON file.
- Use **File → Save Session** to save the entire session (files, annotations, tags).
- Load sessions via **File → Load Session...**.

## Advanced Features

### Managing Entity Tags and Relation Types
- Use **Settings → Manage Entity Tags...** or **Manage Relation Types...** to add, remove, or edit tags/types.
- Save/load schemas via **Settings → Save Tag/Relation Schema...** or **Load Tag/Relation Schema...**.

### Entity Propagation
- Click **Propagate Entities** to copy entities from the current file to all files.
- Use **Settings → Load Dictionary & Propagate Entities...** to annotate from a dictionary file (format: `text tag`, e.g., `John Person`).

### Entity Merging/Demerging
- Select multiple entities and click **Merge Sel.** to assign them the same ID.
- Right-click an annotated span and select **Demerge This Instance** to assign a new ID.

### AI Pre-annotation
- Press `a` or go to **Settings → Pre-annotate with AI...** to tag entities using a pre-trained NER model.
- Requires `transformers` and `torch`. Annotations are marked as propagated (underlined).

### Import/Export
- Export annotations via **File → Export for Training...** in CoNLL or JSONL format.
- Import annotations via **File → Import Annotations...** from CoNLL or JSONL files, creating new `.txt` files.

### Multi-label Annotations
- Enable **Settings → Allow Multi-label & Overlapping Annotations** to permit overlapping tags.

## Data Format

Annotations are stored in JSON format:

```json
{
  "file1.txt": {
    "entities": [
      {
        "id": "a1b2c3...",
        "start_line": 1,
        "start_char": 10,
        "end_line": 1,
        "end_char": 20,
        "text": "John Smith",
        "tag": "Person",
        "propagated": false
      }
    ],
    "relations": [
      {
        "id": "d4e5f6...",
        "type": "works_at",
        "head_id": "a1b2c3...",
        "tail_id": "g7h8i9..."
      }
    ]
  }
}
```

Session files include additional metadata:

```json
{
  "version": "1.12",
  "files_list": ["file1.txt", "file2.txt"],
  "current_file_index": 0,
  "entity_tags": ["Person", "Organization", ...],
  "relation_types": ["spouse_of", "works_at", ...],
  "tag_colors": {"Person": "#ffcccc", ...},
  "annotations": {...},
  "extend_to_word": true,
  "allow_multilabel_overlap": true
}
```

## Tips & Tricks

- **Hotkeys**: Use 0-9 to select/relabel tags, `a` for AI pre-annotation, and `Delete` to remove entities/relations.
- **Navigation**: Click column headers to sort Entities/Relations lists; type a letter to jump to matching items.
- **Workflow**: Annotate entities first, then relations; propagate entities early to save time.
- **Dictionary Format**: Use one entity per line (e.g., `New York Location`).
- **Double-click**: Selects a word for quick annotation.
- **Read-only Text**: Ensures no accidental edits; use mouse or hotkeys for actions.

## Troubleshooting

- **AI Pre-annotation Fails**: Install `transformers` and `torch`; ensure a file is loaded.
- **Missing Files**: Session loading warns about missing files; continue with available ones.
- **Overlap Issues**: Enable multi-label support in Settings for overlapping annotations.
- **Highlighting Issues**: Switch files to refresh the display.
- **Export Errors**: Check write permissions and use `.conll` or `.jsonl` extensions.

## Version History

- **1.12** (2025):
  - Added AI pre-annotation with `Babelscape/wikineural-multilingual-ner`.
  - Implemented multi-label and overlapping annotation support.
  - Added demerge functionality via right-click.
  - Made text area read-only to prevent accidental edits.
  - Improved propagation with whitespace handling and underlining for propagated entities.
  - Enhanced double-click/highlight annotation and single-click removal.
  - Added import/export for CoNLL and spaCy JSONL formats.
- **0.75**: Double-click and highlight annotation, immutable text area.
- **0.70**: Propagated entities flagged and underlined.
- **0.65**: Entity search and sorting.
- **0.60**: Session save/load for continuous work.

## Cite

### APA Style
Kovács, T. (2025). *ANNIE: Annotation Interface for Named-entity & Information Extraction* (Version 1.12) [Computer software]. GitHub. https://github.com/kreeedit/ANNIE

### BibTeX
```bibtex
@software{Kovacs_ANNIE_2025,
  author = {Kovács, Tamás},
  title = {{ANNIE: Annotation Interface for Named-entity & Information Extraction}},
  version = {1.12},
  publisher = {Zenodo},
  year = {2025},
  doi = {10.5281/zenodo.15805548},
  url = {https://github.com/kreeedit/ANNIE}
}
```

## License

Apache 2.0