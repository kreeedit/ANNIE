# -*- coding: utf-8 -*-
import tkinter as tk
from tkinter import filedialog
from tkinter import messagebox
import json
import uuid
import re
import traceback
from bisect import bisect_left, bisect_right
import xml.etree.ElementTree as ET
import os

class ImportMixin:
    """Import + CoNLL/JSONL/CEI-XML parsing."""

    def import_annotations(self):
        import_path = filedialog.askopenfilename(
            title="Select Annotation File to Import",
            filetypes=[("All Supported Formats", "*.conll *.jsonl *.xml"), ("CoNLL Files", "*.conll"), ("JSONL Files", "*.jsonl"), ("XML Files", "*.xml")],
            parent=self.root)
        if not import_path: return
        try:
            parsed_docs, found_tags = [], set()
            if import_path.lower().endswith(".conll"): parsed_docs, found_tags = self._parse_conll_into_documents(import_path)
            elif import_path.lower().endswith(".jsonl"): parsed_docs, found_tags = self._parse_jsonl_into_documents(import_path)
            elif import_path.lower().endswith(".xml"): parsed_docs, found_tags = self._parse_cei_xml_into_documents(import_path)
            else:
                messagebox.showwarning("Unsupported Format", "Please select a .conll, .jsonl or .xml file.")
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

            # For CEI XML files, also strip the .cei.xml extension
            import_name = os.path.basename(import_path)
            if import_name.lower().endswith('.cei.xml'):
                base_name_for_docs = import_name[:-8]  # .cei.xml = 8 characters
            else:
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

    def _parse_cei_xml_into_documents(self, file_path):
        """
        Processes CEI XML file into documents.
        Extracts text from cei:tenor and automatically annotates
        diplomatic elements (place names, dates, etc.).
        """
        # Register CEI namespace
        ET.register_namespace('cei', 'http://www.monasterium.net/NS/cei')
        ET.register_namespace('atom', 'http://www.w3.org/2005/Atom')

        documents = []
        all_tags = set()

        try:
            # Parse XML file
            tree = ET.parse(file_path)
            root = tree.getroot()

            # Find cei:text element
            text_elem = root.find('.//{http://www.monasterium.net/NS/cei}text')
            if text_elem is None:
                messagebox.showwarning("XML Error", f"No cei:text element found in {file_path}")
                return documents, all_tags

            # Extract text from cei:tenor
            tenor_elem = text_elem.find('.//{http://www.monasterium.net/NS/cei}tenor')
            abstract_elem = text_elem.find('.//{http://www.monasterium.net/NS/cei}abstract')

            # Extract and process text
            full_text = ""
            annotations = []

            if tenor_elem is not None:
                tenor_text = self._extract_text_from_cei_element(tenor_elem)
                if tenor_text.strip():
                    full_text = tenor_text
            elif abstract_elem is not None:
                abstract_text = self._extract_text_from_cei_element(abstract_elem)
                if abstract_text.strip():
                    full_text = abstract_text
            else:
                # If no tenor or abstract, try to collect all text
                full_text = self._extract_all_text(text_elem)

            if not full_text.strip():
                messagebox.showinfo("Info", f"No text content found in {file_path}")
                return documents, []

            # CEI XML import: we extract the text, and automatic annotation
            # only works if placeName/dateRange text exactly matches
            # the text in the document.
            # Currently we only extract the text; annotations are added
            # later manually or via AI-based prediction.

            # Extract place names (LOC tag) - for informational purposes
            place_names = []
            for place_elem in text_elem.findall('.//{http://www.monasterium.net/NS/cei}placeName'):
                place_text = self._get_element_text(place_elem)
                if place_text.strip():
                    place_names.append(place_text.strip())
                    all_tags.add('LOC')

            # Extract dates (DAT/TIM tag) - for informational purposes
            date_ranges = []
            for date_elem in text_elem.findall('.//{http://www.monasterium.net/NS/cei}dateRange'):
                date_text = self._get_element_text(date_elem)
                if date_text.strip():
                    date_ranges.append(date_text.strip())
                    all_tags.add('DAT')

            # Extract identifier from atom:id
            atom_id_elem = root.find('.//{http://www.w3.org/2005/Atom}id')
            doc_id = atom_id_elem.text if atom_id_elem is not None else os.path.basename(file_path)

            # Attempt automatic annotation
            line_starts = [0]
            for i, char in enumerate(full_text):
                if char == '\n': line_starts.append(i + 1)
            line_starts.append(len(full_text) + 1)

            def offset_to_tkinter_index(offset):
                line_idx = bisect_right(line_starts, offset) - 1
                line = line_idx + 1
                char = offset - line_starts[line_idx]
                return f"{line}.{char}"

            # Annotate place names (only if place_name is found exactly in the text)
            for place_name in place_names:
                # Find the place_name in the text
                idx = full_text.find(place_name)
                if idx != -1:
                    start_pos = idx
                    end_pos = idx + len(place_name)
                    annotations.append({
                        'start': start_pos,
                        'end': end_pos,
                        'tag': 'LOC'
                    })

            # Annotate dates
            for date_text in date_ranges:
                idx = full_text.find(date_text)
                if idx != -1:
                    start_pos = idx
                    end_pos = idx + len(date_text)
                    annotations.append({
                        'start': start_pos,
                        'end': end_pos,
                        'tag': 'DAT'
                    })

            documents.append({
                'text': full_text,
                'annotations': annotations,
                'source_id': doc_id
            })

        except ET.ParseError as e:
            messagebox.showerror("XML Parse Error", f"Could not parse XML file:\n{e}", parent=self.root)
        except Exception as e:
            messagebox.showerror("Import Error", f"Error processing CEI XML file:\n{e}", parent=self.root)
            traceback.print_exc()

        return documents, all_tags

    def _convert_cei_xml_to_txt(self, xml_path, output_dir=None):
        """
        Converts CEI XML file to TXT file.
        Extracts text from XML and saves it to a TXT file.
        Returns the path to the new TXT file, or None if conversion fails.
        """
        try:
            # Parse XML file
            tree = ET.parse(xml_path)
            root = tree.getroot()

            # Find cei:text element
            text_elem = root.find('.//{http://www.monasterium.net/NS/cei}text')
            if text_elem is None:
                messagebox.showwarning("XML Error", f"No cei:text element found in {xml_path}", parent=self.root)
                return None

            # Extract text from cei:tenor or cei:abstract
            tenor_elem = text_elem.find('.//{http://www.monasterium.net/NS/cei}tenor')
            abstract_elem = text_elem.find('.//{http://www.monasterium.net/NS/cei}abstract')

            full_text = ""
            if tenor_elem is not None:
                full_text = self._extract_text_from_cei_element(tenor_elem)
            elif abstract_elem is not None:
                full_text = self._extract_text_from_cei_element(abstract_elem)
            else:
                # If no tenor or abstract, try to collect all text
                full_text = self._extract_all_text(text_elem)

            if not full_text.strip():
                messagebox.showinfo("Info", f"No text content found in {xml_path}", parent=self.root)
                return None

            # If no output_dir, use the XML file's directory
            if output_dir is None:
                output_dir = os.path.dirname(xml_path)

            # New filename: the XML filename with .txt extension
            base_name = os.path.splitext(os.path.basename(xml_path))[0]
            # If the name ends with .cei, remove it
            if base_name.lower().endswith('.cei'):
                base_name = base_name[:-4]
            output_filename = f"{base_name}.txt"
            output_path = os.path.join(output_dir, output_filename)

            # Save to TXT file
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(full_text.strip())

            self.status_var.set(f"Converted: {os.path.basename(xml_path)} -> {output_filename}")
            return output_path

        except ET.ParseError as e:
            messagebox.showerror("XML Parse Error", f"Could not parse XML file:\n{e}", parent=self.root)
            return None
        except Exception as e:
            messagebox.showerror("Conversion Error", f"Error converting XML to TXT:\n{e}", parent=self.root)
            traceback.print_exc()
            return None

    def _extract_text_from_cei_element(self, element):
        """
        Extracts text from a CEI element, preserving formatting.
        Handles cei:lb, cei:sup, cei:quote, and other elements.
        Normalizes pretty-print whitespace (newlines + indentation from
        the XML formatting are collapsed), but keeps explicit <cei:lb> newlines.
        """
        if element is None:
            return ""

        # Process recursively (avoid self._get_element_text — that is NOT recursive)
        def process_element(elem):
            try:
                result = []
                # Text from element - only non-whitespace
                if elem.text and elem.text.strip():
                    result.append(elem.text.strip() + ' ')
                elif elem.text:
                    result.append(elem.text)

                # Process children
                for child in elem:
                    tag_name = child.tag.split('}')[-1] if '}' in child.tag else child.tag
                    if tag_name == 'lb':
                        result.append('\n')
                    elif tag_name == 'sup':
                        # Keep superscript as simple text (use recursive extraction)
                        sup_text = process_element(child)
                        if sup_text.strip():
                            result.append(sup_text)
                    elif tag_name == 'quote':
                        # Surround quotes with double quotes
                        quote_text = process_element(child)
                        if quote_text.strip():
                            result.append(f'"{quote_text.strip()}" ')
                    elif tag_name == 'abbr':
                        # Expand abbreviations if expan attribute is present
                        expan = child.get('expan')
                        if expan:
                            result.append(expan)
                        else:
                            result.append(process_element(child))
                    elif tag_name == 'expan':
                        # Expanded word
                        result.append(process_element(child))
                    elif tag_name == 'app':
                        # Critical apparatus - lemma text is the main text, or first rdg
                        lemma = child.find('{http://www.monasterium.net/NS/cei}lem')
                        if lemma is not None:
                            result.append(process_element(lemma))
                        else:
                            # If no lem, use first rdg (reading)
                            rdg = child.find('{http://www.monasterium.net/NS/cei}rdg')
                            if rdg is not None:
                                result.append(process_element(rdg))
                    elif tag_name in ('del', 'metamark', 'figure', 'pict', 'anchor', 'ref',
                                       'note', 'cit', 'note'):
                        # Skip these
                        pass
                    else:
                        # Other elements - recursive call
                        result.append(process_element(child))

                    # Tail after child element - only non-whitespace
                    if child.tail and child.tail.strip():
                        result.append(child.tail.strip() + ' ')
                    elif child.tail:
                        result.append(child.tail)

                return ''.join(result)
            except Exception:
                # Fallback: return plain text content if anything goes wrong
                return ''.join(elem.itertext()) if elem is not None else ""

        raw = process_element(element)
        # Clean up pretty-print whitespace: collapse multiple spaces/tabs,
        # strip whitespace around newlines (but keep the newlines from <lb>),
        # collapse consecutive blank lines
        cleaned = re.sub(r'[ \t]{2,}', ' ', raw)
        cleaned = re.sub(r'[ \t]*\n[ \t]*', '\n', cleaned)
        cleaned = re.sub(r'\n{3,}', '\n\n', cleaned)
        return cleaned.strip()

    def extract_diplomatic_parts(self):
        """Extract diplomatic parts from CEI XML files into the current session.

        User selects a directory → ANNIE scans all .xml files → discovers diplomatic
        parts → dialog lets user pick files + parts → either:
          ① create new TXT files and add them to the session, OR
          ② annotate existing session files with diplomatic parts.
        Works even in an empty session (will save TXT files instead).
        """
        if self.files_list:
            session_dir = os.path.dirname(self.files_list[0])
        else:
            # Empty session: ask the user for a save directory first
            session_dir = filedialog.askdirectory(
                title="Select Directory for Extracted TXT Files",
                parent=self.root)
            if not session_dir:
                return

        xml_dir = filedialog.askdirectory(
            title="Select Directory with CEI XML Files",
            parent=self.root)
        if not xml_dir:
            return

        # Find all XML files
        xml_files = sorted([
            os.path.join(xml_dir, f) for f in os.listdir(xml_dir)
            if f.lower().endswith('.xml') and os.path.isfile(os.path.join(xml_dir, f))
        ])

        if not xml_files:
            messagebox.showinfo("No XML Files",
                                f"No .xml files found in:\n{xml_dir}",
                                parent=self.root)
            return

        # Process each XML: discover parts per file
        ns = {'cei': 'http://www.monasterium.net/NS/cei'}
        file_parts_list = []  # list of (filename, file_path, [part_dicts])

        for xml_path in xml_files:
            try:
                tree = ET.parse(xml_path)
                root = tree.getroot()
                text_elem = root.find('.//cei:text', ns)
                if text_elem is None:
                    continue

                parts = self._discover_diplomatic_parts(root, ns, xml_path)
                if parts:
                    file_parts_list.append((os.path.basename(xml_path), xml_path, parts))
            except (ET.ParseError, Exception):
                continue  # skip malformed XMLs silently

        if not file_parts_list:
            messagebox.showinfo("No Diplomatic Parts Found",
                                "No CEI diplomatic parts found in any XML file in:\n"
                                f"{xml_dir}",
                                parent=self.root)
            return

        # Compute session file stems for annotation-matching
        session_stems = set()
        for fp in self.files_list:
            base = os.path.basename(fp)
            if base.lower().endswith('.txt'):
                session_stems.add(base[:-4])
        self._show_diplomatic_extraction_dialog(
            file_parts_list, session_dir, session_stems)

    def _show_diplomatic_extraction_dialog(self, file_parts_list, session_dir,
                                           session_stems=None):
        """Dialog: select part types (top) and files (bottom) to extract.

        Redesigned so the user picks which part TYPE(s) to extract in one
        place (e.g. 'abstract', 'tenor'), and then which FILE(s) from the
        list.  No more per-file per-part checkboxes.
        """
        dialog = tk.Toplevel(self.root)
        dialog.title("Extract Diplomatic Parts from CEI XML")
        dialog.geometry("750x600")
        dialog.transient(self.root)
        dialog.grab_set()

        main_frame = tk.Frame(dialog, padx=15, pady=10)
        main_frame.pack(fill=tk.BOTH, expand=True)

        tk.Label(main_frame,
                 text=f"Found diplomatische Teile in {len(file_parts_list)} XML file(s).\n"
                      "Select part types (above) and files (below) to extract.",
                 font=('TkDefaultFont', 10, 'bold'), justify=tk.LEFT).pack(
            anchor=tk.W, pady=(0, 10))

        # --- Collect unique part types across all files ------------------------
        part_type_to_info = {}  # label -> {'preview': str, 'count': int, 'total_chars': int}
        for fname, fpath, parts in file_parts_list:
            for p in parts:
                label = p['label']
                if label not in part_type_to_info:
                    part_type_to_info[label] = {
                        'preview': p['preview'],
                        'count': 0,
                        'total_chars': 0,
                    }
                part_type_to_info[label]['count'] += 1
                part_type_to_info[label]['total_chars'] += len(p['text'])

        sorted_labels = sorted(part_type_to_info.keys(),
                               key=lambda l: -part_type_to_info[l]['count'])

        # ====================================================================
        # TOP: Part-type selection
        # ====================================================================
        part_container = tk.LabelFrame(main_frame, text="Part Types to Extract",
                                       font=('TkDefaultFont', 9, 'bold'),
                                       padx=8, pady=5)
        part_container.pack(fill=tk.BOTH, expand=True, pady=(0, 5))

        part_canvas_frame = tk.Frame(part_container)
        part_canvas_frame.pack(fill=tk.BOTH, expand=True)

        part_canvas = tk.Canvas(part_canvas_frame, highlightthickness=0, borderwidth=0)
        part_scrollbar = tk.Scrollbar(part_canvas_frame, orient=tk.VERTICAL,
                                       command=part_canvas.yview)
        part_scrollable = tk.Frame(part_canvas)

        part_scrollable.bind(
            '<Configure>',
            lambda e: part_canvas.configure(scrollregion=part_canvas.bbox('all')))
        part_canvas.bind(
            '<Configure>',
            lambda e: part_canvas.itemconfig('inner', width=e.width))
        part_canvas.create_window((0, 0), window=part_scrollable, anchor='nw', tags='inner')
        part_canvas.configure(yscrollcommand=part_scrollbar.set)
        part_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        part_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        part_type_vars = {}
        for label in sorted_labels:
            info = part_type_to_info[label]
            var = tk.BooleanVar(value=True)
            part_type_vars[label] = var

            row = tk.Frame(part_scrollable)
            row.pack(fill=tk.X, padx=5, pady=1)

            cb = tk.Checkbutton(row, variable=var)
            cb.pack(side=tk.LEFT)

            tk.Label(row,
                     text=(f"{label}  —  {info['count']}/{len(file_parts_list)} files, "
                           f"~{info['total_chars']} chars total"),
                     font=('TkDefaultFont', 9, 'bold')).pack(side=tk.LEFT, anchor=tk.W)

            tk.Label(row, text=info['preview'],
                     anchor=tk.W, justify=tk.LEFT, wraplength=600,
                     fg='#666666', font=('TkDefaultFont', 8)).pack(
                fill=tk.X, padx=(20, 0))

        # ====================================================================
        # BOTTOM: File selection
        # ====================================================================
        file_container = tk.LabelFrame(main_frame, text="Files to Include",
                                       font=('TkDefaultFont', 9, 'bold'),
                                       padx=8, pady=5)
        file_container.pack(fill=tk.BOTH, expand=True, pady=(5, 0))

        file_canvas_frame = tk.Frame(file_container)
        file_canvas_frame.pack(fill=tk.BOTH, expand=True)

        file_canvas = tk.Canvas(file_canvas_frame, highlightthickness=0, borderwidth=0)
        file_scrollbar = tk.Scrollbar(file_canvas_frame, orient=tk.VERTICAL,
                                       command=file_canvas.yview)
        file_scrollable = tk.Frame(file_canvas)

        file_scrollable.bind(
            '<Configure>',
            lambda e: file_canvas.configure(scrollregion=file_canvas.bbox('all')))
        file_canvas.bind(
            '<Configure>',
            lambda e: file_canvas.itemconfig('inner', width=e.width))
        file_canvas.create_window((0, 0), window=file_scrollable, anchor='nw', tags='inner')
        file_canvas.configure(yscrollcommand=file_scrollbar.set)
        file_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        file_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        file_vars = {}
        for fname, fpath, parts in file_parts_list:
            var = tk.BooleanVar(value=True)
            file_vars[fname] = var

            row = tk.Frame(file_scrollable)
            row.pack(fill=tk.X, padx=5, pady=1)

            cb = tk.Checkbutton(row, variable=var)
            cb.pack(side=tk.LEFT)

            tk.Label(row, text=f"{fname}  —  {len(parts)} part(s)",
                     font=('TkDefaultFont', 9)).pack(side=tk.LEFT, padx=(3, 0))

        # ====================================================================
        # Bottom bar: quick-select buttons + Export
        # ====================================================================
        btn_bar = tk.Frame(main_frame)
        btn_bar.pack(fill=tk.X, pady=(8, 5))

        tk.Button(btn_bar, text="Parts: All", width=10,
                  command=lambda: self._set_all(part_type_vars, True)).pack(
            side=tk.LEFT, padx=(0, 3))
        tk.Button(btn_bar, text="Parts: None", width=10,
                  command=lambda: self._set_all(part_type_vars, False)).pack(
            side=tk.LEFT, padx=(0, 10))
        tk.Button(btn_bar, text="Files: All", width=10,
                  command=lambda: self._set_all(file_vars, True)).pack(
            side=tk.LEFT, padx=(0, 3))
        tk.Button(btn_bar, text="Files: None", width=10,
                  command=lambda: self._set_all(file_vars, False)).pack(
            side=tk.LEFT)

        tk.Label(btn_bar,
                 text=f"Session dir: {session_dir}",
                 fg='grey', font=('TkDefaultFont', 8)).pack(
            side=tk.RIGHT, padx=(10, 0))

        # ====================================================================
        # Mode selection: annotate existing files vs. create new TXT files
        # ====================================================================
        annotate_mode_var = tk.BooleanVar(value=False)
        if session_stems:
            mode_frame = tk.Frame(main_frame)
            mode_frame.pack(fill=tk.X, pady=(5, 0))

            tk.Checkbutton(
                mode_frame,
                text="Annotate matching session files with diplomatic parts",
                variable=annotate_mode_var,
                font=('TkDefaultFont', 9, 'bold'),
            ).pack(side=tk.LEFT, padx=(5, 0))

            tk.Label(
                mode_frame,
                text="(instead of creating new TXT files)",
                fg='grey', font=('TkDefaultFont', 8),
            ).pack(side=tk.LEFT, padx=(3, 0))

        bottom_frame = tk.Frame(main_frame)
        bottom_frame.pack(fill=tk.X, pady=(5, 0))

        def do_extract():
            selected_labels = {l for l, v in part_type_vars.items() if v.get()}
            if not selected_labels:
                messagebox.showwarning("No Parts Selected",
                                       "Select at least one part type.",
                                       parent=dialog)
                return

            selected_parts = []  # list of (fname, fpath, label, text, base_name)
            for fname, fpath, parts in file_parts_list:
                if not file_vars.get(fname, tk.BooleanVar()).get():
                    continue
                base_name = os.path.splitext(fname)[0]
                if base_name.lower().endswith('.cei'):
                    base_name = base_name[:-4]
                for part in parts:
                    if part['label'] in selected_labels:
                        selected_parts.append(
                            (fname, fpath, part['label'], part['text'], base_name))

            if not selected_parts:
                messagebox.showwarning("No Selection",
                                       "No files contain the selected part types.",
                                       parent=dialog)
                return

            # --- BRANCH: annotate existing files vs. create new TXT files ----
            if session_stems and annotate_mode_var.get():
                annotation_count = self._apply_diplomatic_annotations(
                    selected_parts, session_stems)
                dialog.destroy()
                msg = (f"Applied {annotation_count} diplomatic annotation(s) "
                       f"to session files.")
                messagebox.showinfo("Success", msg, parent=self.root)
                self.status_var.set(msg)
            else:
                saved_count = 0
                new_files = []
                seen_out = set()
                for fname, fpath, label, text, base_name in selected_parts:
                    safe_label = label.lower().replace(' ', '_').replace('/', '_')
                    out_name = f"{base_name}_{safe_label}.txt"
                    out_path = os.path.join(session_dir, out_name)
                    # Avoid overwriting: add counter suffix if needed
                    counter = 1
                    while out_path in seen_out or (os.path.exists(out_path) and counter < 100):
                        out_path = os.path.join(session_dir,
                                                f"{base_name}_{safe_label}_{counter}.txt")
                        counter += 1
                    try:
                        with open(out_path, 'w', encoding='utf-8') as f:
                            f.write(text)
                        seen_out.add(out_path)
                        saved_count += 1
                        new_files.append(out_path)
                    except Exception as e:
                        messagebox.showerror("Error",
                                             f"Failed to write {out_name}:\n{e}",
                                             parent=dialog)
                        return

                # Add new files to the session
                existing_basenames = {os.path.basename(p) for p in self.files_list}
                truly_new = [p for p in new_files
                             if os.path.basename(p) not in existing_basenames]
                if truly_new:
                    self.files_list.extend(truly_new)
                    self.files_list.sort(key=lambda p: os.path.basename(p).lower())
                    current_path = self.current_file_path
                    self.files_listbox.delete(0, tk.END)
                    for fp in self.files_list:
                        self.files_listbox.insert(tk.END, os.path.basename(fp))
                    if current_path and current_path in self.files_list:
                        idx = self.files_list.index(current_path)
                        self.files_listbox.selection_set(idx)
                        self.files_listbox.see(idx)
                        self.files_listbox.activate(idx)
                    self._update_button_states()

                dialog.destroy()
                msg = (f"Saved {saved_count} diplomatic part(s) to:\n{session_dir}\n\n"
                       f"Added {len(truly_new)} new file(s) to the session.")
                messagebox.showinfo("Success", msg, parent=self.root)
                self.status_var.set(
                    f"Extracted {saved_count} diplomatic part(s), "
                    f"{len(truly_new)} added to session.")

        tk.Button(bottom_frame, text="Export to Session", command=do_extract,
                  bg="lightblue", width=16).pack(side=tk.RIGHT, padx=(5, 0))
        tk.Button(bottom_frame, text="Cancel", command=dialog.destroy,
                  width=8).pack(side=tk.RIGHT)

    @staticmethod
    def _set_all(var_dict, value):
        """Helper: set all BooleanVars in *var_dict* to *value*."""
        for v in var_dict.values():
            v.set(value)

    def _setup_diplomatic_layer(self, tag_names):
        """Ensure the 'Diplomatic' layer exists with the given tag names."""
        if "Diplomatic" not in self.tag_hierarchy:
            self.tag_hierarchy["Diplomatic"] = []
        for tagname in tag_names:
            if tagname not in self.entity_tags:
                self.tag_hierarchy["Diplomatic"].append(tagname)
                self.tag_active_states[tagname] = True
                self.tag_propagation_states[tagname] = True
                self.tag_visible_states[tagname] = True
        self._sync_flat_tags()
        self._ensure_default_colors()
        self._update_entity_tag_combobox()
        self._configure_text_tags()

    @staticmethod
    def _diplomatic_label_to_tag(label):
        """Convert a human-readable diplomatic part label to a short tag name.

        e.g. 'tenor (main text)' → 'tenor', 'abstract / regest' → 'abstract'
        """
        tag = re.sub(r'\([^)]*\)', '', label).strip()
        if '/' in tag:
            tag = tag.split('/')[0].strip()
        tag = tag.strip().replace(' ', '_').replace('-', '_')
        return tag if tag else label

    def _apply_diplomatic_annotations(self, selected_parts, session_stems):
        """Apply diplomatic parts as annotations to matching session files.

        *selected_parts* is a list of (fname, fpath, label, text, base_name).
        For each part, we try to match the XML file's base_name to a session
        file and, if found, search the part text in the file content and
        create an annotation entry.
        Returns the total number of annotations created.
        """
        import uuid
        from bisect import bisect_right

        # Build reverse lookup: session file stem → full path
        stem_to_path = {}
        for fp in self.files_list:
            base = os.path.basename(fp)
            if base.lower().endswith('.txt'):
                stem = base[:-4]
                stem_to_path[stem] = fp

        # Collect all tag names used so we can set up the Diplomatic layer
        used_tags = set()
        # Group annotations per file path
        file_annotations_map = {}  # file_path → list of annotation dicts

        for fname, fpath, label, text, xml_stem in selected_parts:
            # Find matching session file
            session_path = stem_to_path.get(xml_stem)
            if not session_path:
                # Try fuzzy matching: if xml_stem has a prefix the TXT doesn't
                for stem, fp in stem_to_path.items():
                    if stem in xml_stem or xml_stem in stem:
                        session_path = fp
                        break
            if not session_path:
                continue

            tag_name = self._diplomatic_label_to_tag(label)
            used_tags.add(tag_name)

            # Read the TXT file content
            try:
                with open(session_path, 'r', encoding='utf-8') as f:
                    content = f.read()
            except Exception:
                continue

            # Normalize both text and content for matching
            def normalize(s):
                return ' '.join(s.split())

            # Try exact match first, then normalized match
            part_text = text
            match_pos = content.find(part_text)
            if match_pos == -1:
                norm_part = normalize(part_text)
                norm_content = normalize(content)
                match_pos = norm_content.find(norm_part)
                if match_pos == -1:
                    continue  # text not found — skip
                # We found the position in normalized text, but we need the
                # offset in the original content.  Approximate by finding
                # the norm_part substring that bridges whitespace differences.
                # Fallback: search for the first 40 chars (uncommon enough
                # to be unique, common enough to survive normalization).
                short_prefix = normalize(part_text[:40])
                match_pos = normalize(content).find(short_prefix)
                if match_pos == -1:
                    continue

                # Now that we have a position in normalized content, recover
                # original offset by scanning forward until the char matches
                # content char by char
                raw_pos = 0
                norm_idx = 0
                while norm_idx < match_pos and raw_pos < len(content):
                    if content[raw_pos].isspace():
                        raw_pos += 1
                    else:
                        if not content[raw_pos].isspace():
                            norm_idx += 1
                        raw_pos += 1
                match_pos = raw_pos

            # Compute tkinter indices for the matched position
            line_starts = [0]
            for i, ch in enumerate(content):
                if ch == '\n':
                    line_starts.append(i + 1)
            line_starts.append(len(content) + 1)

            end_pos = match_pos + len(part_text)
            # Clamp to content length
            end_pos = min(end_pos, len(content))

            start_str = self._char_offset_to_tkinter_index_from_offsets(
                line_starts, match_pos)
            end_str = self._char_offset_to_tkinter_index_from_offsets(
                line_starts, end_pos)

            try:
                start_l, start_c = map(int, start_str.split('.'))
                end_l, end_c = map(int, end_str.split('.'))
            except ValueError:
                continue

            annotation = {
                'id': uuid.uuid4().hex,
                'start_line': start_l,
                'start_char': start_c,
                'end_line': end_l,
                'end_char': end_c,
                'text': content[match_pos:end_pos],
                'tag': tag_name,
                'propagated': False,
            }
            file_annotations_map.setdefault(session_path, []).append(annotation)

        if not file_annotations_map:
            messagebox.showinfo("No Matches",
                                "Could not match any CEI XML files to session TXT files. "
                                "Make sure the XML filenames correspond to session TXT files "
                                "(e.g. 'charta_01.cei.xml' ↔ 'charta_01.txt').",
                                parent=self.root)
            return 0

        # Set up the Diplomatic layer with the tags we need
        self._setup_diplomatic_layer(used_tags)

        # Apply annotations to the session data
        total_annotations = 0
        for file_path, new_entities in file_annotations_map.items():
            file_data = self.annotations.setdefault(
                file_path, {"entities": [], "relations": []})
            file_data["entities"].extend(new_entities)
            total_annotations += len(new_entities)

        # Refresh UI if the current file received annotations
        if self.current_file_path in file_annotations_map:
            self._build_entity_lookup_map(
                self.annotations[self.current_file_path].get("entities", []))
            self.apply_annotations_to_text()
            self.update_entities_list()
            self.update_relations_list()
        elif self.current_file_path is None and file_annotations_map:
            # Load the first annotated file
            first_path = next(iter(file_annotations_map))
            if first_path in self.files_list:
                idx = self.files_list.index(first_path)
                self.load_file(idx)

        self._update_button_states()
        return total_annotations

    def _discover_diplomatic_parts(self, root, ns, xml_path):
        """Discover diplomatic parts in a CEI XML file.

        Returns a list of dicts: {'label': ..., 'text': ..., 'preview': ...}
        """
        # Map CEI tag names to human-readable labels
        part_labels = {
            'invocatio': 'invocatio',
            'intitulatio': 'intitulatio',
            'inscriptio': 'inscriptio',
            'arenga': 'arenga',
            'narratio': 'narratio',
            'dispositio': 'dispositio',
            'sanctio': 'sanctio',
            'corroboratio': 'corroboratio',
            'apprecatio': 'apprecatio',
            'eschatocol': 'eschatocol',
            'authenticationFormula': 'authentication formula',
            'tenor': 'tenor (main text)',
            'abstract': 'abstract / regest',
            'datatio': 'datation',
            'publicatio': 'publicatio / promulgatio',
            'promulgatio': 'publicatio / promulgatio',
            'protocol': 'protocol',
            'textBody': 'text body',
        }

        text_elem = root.find('.//cei:text', ns)
        if text_elem is None:
            return []

        parts = []
        for local_name, label in part_labels.items():
            # Use .// for recursive search — in real CEI files diplomatic parts
            # can be nested: cei:text → cei:body → cei:tenor → cei:protocol → cei:invocatio
            # or cei:text → cei:body → cei:chDesc → cei:abstract
            elems = text_elem.findall(f'.//cei:{local_name}', ns)
            for elem in elems:
                text = self._extract_text_from_cei_element(elem)
                if text.strip():
                    preview = (text[:80] + '...') if len(text) > 80 else text
                    parts.append({
                        'label': label,
                        'text': text,
                        'preview': preview,
                    })

        return parts

    def _get_element_text(self, element):
        """
        Extracts text from a CEI element, preserving formatting.
        Returns only direct text and tail, not recursively.
        Used for extracting place names and dates (not full text).
        """
        if element is None:
            return ""
        parts = []
        # Direct text (not only whitespace)
        if element.text and element.text.strip():
            parts.append(element.text.strip())
        elif element.text:
            parts.append(element.text)
        # Tail if exists
        if element.tail and element.tail.strip():
            parts.append(element.tail.strip())
        elif element.tail:
            parts.append(element.tail)
        return ' '.join(parts).strip()

    def _extract_all_text(self, element):
        """
        Extracts all text from an element, preserving newlines.
        """
        if element is None:
            return ""
        parts = []
        if element.text:
            parts.append(element.text)
        for child in element:
            if child.tag.endswith('}lb') or child.tag == 'lb':
                parts.append('\n')
            parts.append(self._extract_all_text(child))
            if child.tail:
                parts.append(child.tail)
        return ''.join(parts)
