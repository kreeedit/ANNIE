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
        Normalizes text (multiple whitespace -> single space).
        """
        if element is None:
            return ""

        # Process recursively
        def process_element(elem):
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
                    # Keep superscript but as simple text
                    sup_text = self._get_element_text(child)
                    if sup_text:
                        result.append(sup_text)
                elif tag_name == 'quote':
                    # Surround quotes with double quotes
                    quote_text = self._get_element_text(child)
                    if quote_text:
                        result.append(f'"{quote_text}"')
                elif tag_name == 'abbr':
                    # Expand abbreviations if expan attribute is present
                    expan = child.get('expan')
                    if expan:
                        result.append(expan)
                    else:
                        result.append(self._get_element_text(child))
                elif tag_name == 'expan':
                    # Expanded word
                    result.append(self._get_element_text(child))
                elif tag_name == 'app':
                    # Critical apparatus - lemma text is the main text, or first rdg
                    lemma = child.find('{http://www.monasterium.net/NS/cei}lem')
                    if lemma is not None:
                        result.append(self._get_element_text(lemma))
                    else:
                        # If no lem, use first rdg (reading)
                        rdg = child.find('{http://www.monasterium.net/NS/cei}rdg')
                        if rdg is not None:
                            result.append(self._get_element_text(rdg))
                elif tag_name in ['del', 'metamark', 'figure', 'pict', 'anchor', 'ref']:
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

        return process_element(element).strip()

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
