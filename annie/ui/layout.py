# -*- coding: utf-8 -*-
import tkinter as tk
from tkinter import ttk
import time
from bisect import bisect_left, bisect_right

class LayoutMixin:
    """Main UI layout + treeview/click helpers."""

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
        self.files_listbox.bind('<Button-3>', self._on_files_right_click)
        self.files_listbox.bind('<Button-2>', self._on_files_right_click)
        scrollbar_files.config(command=self.files_listbox.yview)
        nav_frame = tk.Frame(left_frame)
        nav_frame.pack(fill=tk.X, pady=5)
        self.prev_btn = tk.Button(nav_frame, text="Previous", command=self.load_previous_file, state=tk.DISABLED)
        self.prev_btn.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 2))
        self.next_btn = tk.Button(nav_frame, text="Next", command=self.load_next_file, state=tk.DISABLED)
        self.next_btn.pack(side=tk.RIGHT, fill=tk.X, expand=True, padx=(2, 0))

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
        self.text_area = tk.Text(text_frame, wrap=tk.WORD, yscrollcommand=scrollbar_text_y.set,
                                 xscrollcommand=scrollbar_text_x.set, undo=True, state=tk.DISABLED,
                                 borderwidth=1, relief="sunken", insertbackground="black", insertwidth=2,
                                 takefocus=False)
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
        self.entities_tree = ttk.Treeview(entities_tree_frame, columns=("ID", "Start", "End", "Text", "Tag"),
                                          displaycolumns=("Start", "End", "Text", "Tag"), show="headings",
                                          yscrollcommand=scrollbar_entities_y.set, selectmode='extended')
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
        self.relations_tree = ttk.Treeview(relations_tree_frame, columns=("ID", "Head", "Type", "Tail"),
                                           displaycolumns=("Head", "Type", "Tail"), show="headings",
                                           yscrollcommand=scrollbar_relations_y.set, selectmode='browse')
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
        items = tree.get_children("")
        if col in ["Start", "End"] and tree == self.entities_tree:
            data = [(tuple(map(int, tree.set(item, col).split('.'))), item)
                    if tree.set(item, col) else ((0, 0), item) for item in items]
        else:
            data = [(tree.set(item, col).lower(), item) for item in items]

        data.sort(reverse=reverse)
        for index, (_, item) in enumerate(data): tree.move(item, "", index)
        valid_selection = [s for s in tree.selection() if tree.exists(s)]
        if valid_selection:
            tree.selection_set(valid_selection)
            tree.see(valid_selection[0])
        else:
            if tree == self.entities_tree: self.selected_entity_ids_for_relation = []
            self._update_button_states()

        for column_id in tree["displaycolumns"]:
            tree.heading(column_id, text=tree.heading(column_id, 'text').replace(" ▲", "").replace(" ▼", ""))
        indicator = "▼" if reverse else "▲"
        tree.heading(col, text=f"{tree.heading(col, 'text').replace(' ▲', '').replace(' ▼', '')} {indicator}",
                     command=lambda c=col: self._treeview_sort_column(tree, c, not reverse))

    def _treeview_key_navigate(self, tree, event):
        if not event.char or not event.char.isprintable() or len(event.char) != 1: return
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
        if not self.current_file_path: return
        CLICK_TIME_THRESHOLD = 0.5
        CLICK_MOVE_THRESHOLD = 10
        time_diff = time.time() - self._click_time
        move_diff = abs(event.x - self._click_pos[0]) + abs(event.y - self._click_pos[1])
        try:
            sel_start = self.text_area.index(tk.SEL_FIRST)
            sel_end = self.text_area.index(tk.SEL_LAST)
            if sel_start != sel_end:
                self.annotate_selection()
                return
        except tk.TclError: pass

        if time_diff < CLICK_TIME_THRESHOLD and move_diff < CLICK_MOVE_THRESHOLD:
            if self._just_double_clicked:
                self._just_double_clicked = False
                return
            original_state = self.text_area.cget('state')
            self.text_area.config(state=tk.NORMAL)
            try:
                click_index_str = self.text_area.index(f"@{event.x},{event.y}")
                click_pos = tuple(map(int, click_index_str.split('.')))
                entities = self.annotations.get(self.current_file_path, {}).get("entities", [])

                sorted_entities = sorted(entities, key=lambda e: (e['start_line'], e['start_char']))
                start_positions = [(e['start_line'], e['start_char']) for e in sorted_entities]
                idx = bisect_left(start_positions, click_pos)
                clicked_entity_dict = None

                for i in range(max(0, idx - 1), min(len(sorted_entities), idx + 1)):
                    entity = sorted_entities[i]
                    start_pos_tuple = (entity['start_line'], entity['start_char'])
                    end_pos_tuple = (entity['end_line'], entity['end_char'])
                    if start_pos_tuple <= click_pos < end_pos_tuple:
                        clicked_entity_dict = entity
                        break

                if clicked_entity_dict:
                    self._remove_entity_instance(clicked_entity_dict)
            except (tk.TclError, ValueError): pass
            finally:
                if self.text_area.winfo_exists():
                    self.text_area.config(state=original_state)

    def _on_double_click(self, event):
        self._just_double_clicked = True
        if not self.current_file_path: return "break"
        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL)
        try:
            click_index_str = self.text_area.index(f"@{event.x},{event.y}")
            click_pos = tuple(map(int, click_index_str.split('.')))
            entities = self.annotations.get(self.current_file_path, {}).get("entities", [])

            sorted_entities = sorted(entities, key=lambda e: (e['start_line'], e['start_char']))
            start_positions = [(e['start_line'], e['start_char']) for e in sorted_entities]
            idx = bisect_left(start_positions, click_pos)
            for i in range(max(0, idx - 1), min(len(sorted_entities), idx + 1)):
                entity = sorted_entities[i]
                start_pos = (entity['start_line'], entity['start_char'])
                end_pos = (entity['end_line'], entity['end_char'])
                if start_pos <= click_pos < end_pos:
                    return "break"

            word_start = self.text_area.index(f"{click_index_str} wordstart")
            word_end = self.text_area.index(f"{click_index_str} wordend")
            if word_start != word_end:
                self.text_area.tag_remove(tk.SEL, "1.0", tk.END)
                self.text_area.tag_add(tk.SEL, word_start, word_end)
                self.annotate_selection()
        except (tk.TclError, ValueError): pass
        finally:
            if self.text_area.winfo_exists():
                self.text_area.config(state=original_state)
        return "break"

    def _remove_entity_instance(self, entity_to_remove):
        if not self.current_file_path or self.current_file_path not in self.annotations: return
        self._handle_entity_deletion([entity_to_remove])
