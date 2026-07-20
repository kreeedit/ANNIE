# -*- coding: utf-8 -*-
import tkinter as tk
from tkinter import messagebox
from tkinter import ttk
import re

class ManageMixin:
    """Entity-tag / relation-type management dialogs."""

    def manage_entity_tags(self):
        window = tk.Toplevel(self.root)
        window.title("Manage Layered Entity Tags")
        window.geometry("650x550")
        window.transient(self.root)
        window.grab_set()

        list_frame = tk.Frame(window)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(10, 5))

        columns = ("Visible", "Count", "Active", "Propagate")
        tree = ttk.Treeview(list_frame, columns=columns, selectmode="browse")
        tree.heading("#0", text="Layer / Tag", anchor=tk.W)
        tree.heading("Visible", text="Visible", anchor=tk.CENTER)
        tree.heading("Count", text="Count", anchor=tk.CENTER)
        tree.heading("Active", text="Active (Hotkeys)", anchor=tk.CENTER)
        tree.heading("Propagate", text="Auto-Propagate", anchor=tk.CENTER)

        tree.column("#0", width=250, anchor=tk.W)
        tree.column("Visible", width=70, anchor=tk.CENTER)
        tree.column("Count", width=60, anchor=tk.CENTER)
        tree.column("Active", width=130, anchor=tk.CENTER)
        tree.column("Propagate", width=120, anchor=tk.CENTER)

        scrollbar = tk.Scrollbar(list_frame, orient=tk.VERTICAL, command=tree.yview)
        tree.configure(yscrollcommand=scrollbar.set)
        tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        def refresh_tree():
            tree.delete(*tree.get_children())
            hotkey_counter = 1

            tag_counts = {}
            for file_path, data in self.annotations.items():
                for entity in data.get("entities", []):
                    t = entity.get("tag")
                    if t: tag_counts[t] = tag_counts.get(t, 0) + 1

            for layer, tags in self.tag_hierarchy.items():
                layer_active = any(self.tag_active_states.get(t, True) for t in tags)
                layer_prop = any(self.tag_propagation_states.get(t, True) for t in tags)
                layer_visible = any(self.tag_visible_states.get(t, True) for t in tags)
                l_vis = "✅ (Layer)" if layer_visible else "❌ (Layer)"
                l_act = "✅ (Layer)" if layer_active else "❌ (Layer)"
                l_prop = "✅ (Layer)" if layer_prop else "❌ (Layer)"
                layer_count = sum(tag_counts.get(t, 0) for t in tags)

                layer_iid = tree.insert("", tk.END, text=layer,
                                        values=(l_vis, layer_count, l_act, l_prop), open=True)

                for tag in tags:
                    is_visible = self.tag_visible_states.get(tag, True)
                    is_active = self.tag_active_states.get(tag, True)
                    is_prop = self.tag_propagation_states.get(tag, True)
                    vis_display = "✅" if is_visible else "❌"
                    act_display = "❌"
                    if is_active:
                        if hotkey_counter <= 10:
                            num = hotkey_counter if hotkey_counter < 10 else 0
                            act_display = f"✅ (Key: {num})"
                            hotkey_counter += 1
                        else: act_display = "✅ (No key)"

                    prop_display = "✅" if is_prop else "❌"
                    count = tag_counts.get(tag, 0)
                    tid = tree.insert(layer_iid, tk.END, text=tag,
                                      values=(vis_display, count, act_display, prop_display))

                    color = self.get_color_for_tag(tag)
                    try: tree.tag_configure(tid, background=color)
                    except: pass
                    tree.item(tid, tags=(tid,))

        refresh_tree()

        def on_tree_double_click(event):
            item_id = tree.identify_row(event.y)
            column = tree.identify_column(event.x)
            if not item_id or column not in ('#1', '#3', '#4'): return

            item_text = tree.item(item_id, 'text')
            parent_id = tree.parent(item_id)
            is_layer = (parent_id == '')

            if column == '#1':
                if is_layer:
                    current_vis = any(self.tag_visible_states.get(t, True) for t in self.tag_hierarchy[item_text])
                    for t in self.tag_hierarchy[item_text]: self.tag_visible_states[t] = not current_vis
                else: self.tag_visible_states[item_text] = not self.tag_visible_states.get(item_text, True)
            elif column == '#3':
                if is_layer:
                    current_active = any(self.tag_active_states.get(t, True) for t in self.tag_hierarchy[item_text])
                    for t in self.tag_hierarchy[item_text]: self.tag_active_states[t] = not current_active
                else: self.tag_active_states[item_text] = not self.tag_active_states.get(item_text, True)
            elif column == '#4':
                if is_layer:
                    current_prop = any(self.tag_propagation_states.get(t, True) for t in self.tag_hierarchy[item_text])
                    for t in self.tag_hierarchy[item_text]: self.tag_propagation_states[t] = not current_prop
                else: self.tag_propagation_states[item_text] = not self.tag_propagation_states.get(item_text, True)

            refresh_tree()
            self._update_entity_tag_combobox()
            self.apply_annotations_to_text()

        tree.bind("<Double-1>", on_tree_double_click)

        controls_frame = tk.Frame(window)
        controls_frame.pack(fill=tk.X, padx=10, pady=10)
        add_frame = tk.Frame(controls_frame)
        add_frame.pack(fill=tk.X, pady=5)
        tk.Label(add_frame, text="New Tag:").pack(side=tk.LEFT)
        new_tag_var = tk.StringVar()
        entry = tk.Entry(add_frame, textvariable=new_tag_var)
        entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)

        def add_tag():
            tag = new_tag_var.get().strip()
            if not tag: return
            if tag in self.entity_tags:
                messagebox.showwarning("Duplicate", "Tag already exists!", parent=window)
                return

            selected = tree.selection()
            if selected:
                item_id = selected[0]
                parent_id = tree.parent(item_id)
                target_layer = tree.item(item_id, 'text') if parent_id == '' else tree.item(parent_id, 'text')
            else: target_layer = list(self.tag_hierarchy.keys())[0]

            self.tag_hierarchy[target_layer].append(tag)
            self.tag_active_states[tag] = True
            self.tag_propagation_states[tag] = True
            self.tag_visible_states[tag] = True
            self._sync_flat_tags()
            refresh_tree()
            self._update_entity_tag_combobox()
            new_tag_var.set("")

        tk.Button(add_frame, text="Add to Selected Layer", command=add_tag).pack(side=tk.LEFT)
        entry.bind("<Return>", lambda e: add_tag())

        btn_frame = tk.Frame(controls_frame)
        btn_frame.pack(fill=tk.X, pady=5)

        def rename_tag():
            selected = tree.selection()
            if not selected: return
            item_id = selected[0]
            if tree.parent(item_id) == '':
                messagebox.showinfo("Info", "Cannot rename entire layers yet, select a Tag.", parent=window)
                return

            old_tag = tree.item(item_id, 'text')
            from tkinter import simpledialog
            new_tag = simpledialog.askstring("Rename / Merge Tag", f"New name for '{old_tag}':\n(If you type an existing tag, they will be merged)", initialvalue=old_tag, parent=window)
            if not new_tag: return
            new_tag = new_tag.strip()
            if not new_tag or new_tag == old_tag: return

            parent_layer = tree.item(tree.parent(item_id), 'text')

            if new_tag in self.entity_tags:
                if not messagebox.askyesno("Merge Tags", f"The tag '{new_tag}' already exists.\n\nDo you want to MERGE all '{old_tag}' annotations into '{new_tag}'?\n\nThis will remove '{old_tag}' from the list entirely.", parent=window): return
                self.tag_hierarchy[parent_layer].remove(old_tag)
                self.tag_active_states.pop(old_tag, None)
                self.tag_propagation_states.pop(old_tag, None)
                self.tag_visible_states.pop(old_tag, None)
                self.tag_colors.pop(old_tag, None)
                self._sync_flat_tags()

                rename_count = 0
                for file_path, data in self.annotations.items():
                    for entity in data.get("entities", []):
                        if entity.get("tag") == old_tag:
                            entity["tag"] = new_tag
                            rename_count += 1
                if self.current_file_path: self._build_entity_lookup_map(self.annotations.get(self.current_file_path, {}).get('entities', []))
                messagebox.showinfo("Merge Successful", f"Successfully merged '{old_tag}' into '{new_tag}'.\nUpdated {rename_count} annotations.", parent=window)
            else:
                idx = self.tag_hierarchy[parent_layer].index(old_tag)
                self.tag_hierarchy[parent_layer][idx] = new_tag
                self.tag_active_states[new_tag] = self.tag_active_states.pop(old_tag, True)
                self.tag_propagation_states[new_tag] = self.tag_propagation_states.pop(old_tag, True)
                self.tag_visible_states[new_tag] = self.tag_visible_states.pop(old_tag, True)
                if old_tag in self.tag_colors: self.tag_colors[new_tag] = self.tag_colors.pop(old_tag)
                self._sync_flat_tags()

                rename_count = 0
                for file_path, data in self.annotations.items():
                    for entity in data.get("entities", []):
                        if entity.get("tag") == old_tag:
                            entity["tag"] = new_tag
                            rename_count += 1
                if self.current_file_path: self._build_entity_lookup_map(self.annotations.get(self.current_file_path, {}).get('entities', []))
                messagebox.showinfo("Rename Successful", f"Renamed to '{new_tag}'.\nUpdated {rename_count} annotations.", parent=window)

            refresh_tree()
            self._update_entity_tag_combobox()

        def delete_tag():
            selected = tree.selection()
            if not selected:
                return
            item_id = selected[0]
            if tree.parent(item_id) == '':
                messagebox.showinfo("Info", "Select a Tag (not a Layer) to delete.", parent=window)
                return
            tag = tree.item(item_id, 'text')
            if not messagebox.askyesno("Delete Tag",
                                       f"Delete tag '{tag}'?\n\n"
                                       "Annotations using this tag will remain "
                                       "but the tag itself will be removed.",
                                       parent=window):
                return
            parent_layer = tree.item(tree.parent(item_id), 'text')
            self.tag_hierarchy[parent_layer].remove(tag)
            self.tag_active_states.pop(tag, None)
            self.tag_propagation_states.pop(tag, None)
            self.tag_visible_states.pop(tag, None)
            self.tag_colors.pop(tag, None)
            self._sync_flat_tags()
            self._update_entity_tag_combobox()
            refresh_tree()

        tk.Button(btn_frame, text="Rename Selected", command=rename_tag).pack(side=tk.LEFT)
        tk.Button(btn_frame, text="Delete Tag", command=delete_tag,
                  width=10).pack(side=tk.LEFT, padx=(5, 0))
        tk.Label(btn_frame, text="(Double-click columns to toggle Visible/Active/Propagate)", fg="grey").pack(side=tk.LEFT, padx=10)

        # --- Layer management buttons ---
        def add_layer():
            from tkinter import simpledialog
            name = simpledialog.askstring("Add Layer", "New layer name:",
                                          parent=window)
            if not name:
                return
            name = name.strip()
            if not name:
                return
            if name in self.tag_hierarchy:
                messagebox.showwarning("Duplicate", f"Layer '{name}' already exists.",
                                       parent=window)
                return
            self.tag_hierarchy[name] = []
            refresh_tree()

        def rename_layer():
            from tkinter import simpledialog
            selected = tree.selection()
            if not selected:
                messagebox.showinfo("No Selection", "Select a layer first.",
                                    parent=window)
                return
            item_id = selected[0]
            if tree.parent(item_id) != '':
                messagebox.showinfo("Not a Layer",
                                    "Select a layer (parent item), not a tag.",
                                    parent=window)
                return
            old_name = tree.item(item_id, 'text')
            new_name = simpledialog.askstring("Rename Layer",
                                              f"New name for layer '{old_name}':",
                                              initialvalue=old_name,
                                              parent=window)
            if not new_name:
                return
            new_name = new_name.strip()
            if not new_name or new_name == old_name:
                return
            if new_name in self.tag_hierarchy:
                messagebox.showwarning("Duplicate",
                                       f"Layer '{new_name}' already exists.",
                                       parent=window)
                return
            self.tag_hierarchy[new_name] = self.tag_hierarchy.pop(old_name)
            refresh_tree()

        def delete_layer():
            selected = tree.selection()
            if not selected:
                messagebox.showinfo("No Selection", "Select a layer first.",
                                    parent=window)
                return
            item_id = selected[0]
            if tree.parent(item_id) != '':
                messagebox.showinfo("Not a Layer",
                                    "Select a layer (parent item), not a tag.",
                                    parent=window)
                return
            layer_name = tree.item(item_id, 'text')
            tags = self.tag_hierarchy[layer_name]
            if tags:
                msg = (f"Delete layer '{layer_name}'?\n\n"
                       f"It contains {len(tags)} tag(s): {', '.join(tags)}.\n"
                       f"All tags in this layer will be removed from the session.")
                if not messagebox.askyesno("Delete Layer", msg, parent=window):
                    return
            else:
                if not messagebox.askyesno("Delete Layer",
                                           f"Delete empty layer '{layer_name}'?",
                                           parent=window):
                    return

            for tag in tags:
                self.tag_active_states.pop(tag, None)
                self.tag_propagation_states.pop(tag, None)
                self.tag_visible_states.pop(tag, None)
                self.tag_colors.pop(tag, None)

            del self.tag_hierarchy[layer_name]
            self._sync_flat_tags()
            self._update_entity_tag_combobox()
            refresh_tree()

        tk.Button(btn_frame, text="Add Layer", command=add_layer,
                  width=10).pack(side=tk.LEFT, padx=(5, 0))
        tk.Button(btn_frame, text="Rename Layer", command=rename_layer,
                  width=10).pack(side=tk.LEFT, padx=(5, 0))
        tk.Button(btn_frame, text="Delete Layer", command=delete_layer,
                  width=10).pack(side=tk.LEFT, padx=(5, 0))

        def save_and_close():
            self._configure_text_tags()
            if self.current_file_path:
                self.apply_annotations_to_text()
                self.update_entities_list()
            window.destroy()

        tk.Button(btn_frame, text="Close", command=save_and_close, width=10).pack(side=tk.RIGHT)
        window.wait_window()

    def manage_relation_types(self):
        self._manage_items("Relation Types", self.relation_types, self._update_relation_type_combobox)

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
            if item_type_name == "Entity Tags" and index < 10:
                hotkey_num = (index + 1) % 10 if (index + 1) % 10 != 0 else 0
                display_text = f"{hotkey_num}: {item}"
            listbox.insert(tk.END, display_text)
        listbox.pack(fill=tk.BOTH, expand=True); scrollbar.config(command=listbox.yview)
        controls_frame = tk.Frame(window); controls_frame.pack(fill=tk.X, padx=10, pady=5)
        item_var = tk.StringVar()
        item_entry = tk.Entry(controls_frame, textvariable=item_var, width=20)
        item_entry.grid(row=0, column=0, sticky="ew", padx=(0, 5))
        controls_frame.grid_columnconfigure(0, weight=1)
        def add_item():
            item = item_var.get().strip()
            if item:
                raw_items = list(listbox.get(0, tk.END))
                existing = [re.sub(r"^\d:\s", "", i).lower() for i in raw_items]
                if item.lower() not in existing:
                    listbox.insert(tk.END, item)
                    updated_items = list(listbox.get(0, tk.END))
                    listbox.delete(0, tk.END)
                    for i_val in sorted(updated_items, key=str.lower): listbox.insert(tk.END, i_val)
                    item_var.set("")
                else: messagebox.showwarning("Duplicate", f"'{item}' already exists.", parent=window)
            item_entry.focus_set()
        item_entry.bind("<Return>", lambda event: add_item())
        tk.Button(controls_frame, text="Add", width=7, command=add_item).grid(row=0, column=1, padx=5)
        def remove_item():
            indices = listbox.curselection()
            if indices:
                for index in sorted(indices, reverse=True): listbox.delete(index)
            else: messagebox.showwarning("No Selection", "Select item(s) to remove.", parent=window)
        tk.Button(controls_frame, text="Remove", width=7, command=remove_item).grid(row=0, column=2)
        button_frame = tk.Frame(window); button_frame.pack(fill=tk.X, padx=10, pady=(5, 10))
        def save_changes():
            new_items_raw = list(listbox.get(0, tk.END))
            new_items = new_items_raw if item_type_name != "Entity Tags" else [re.sub(r"^\d:\s*", "", item) for item in new_items_raw]
            if set(new_items) != set(current_items_list):
                current_items_list[:] = new_items
                update_combobox_func()
                if item_type_name == "Relation Types": self.update_relations_list()
            window.destroy()
        tk.Button(button_frame, text="Save Changes", width=12, command=save_changes).pack(side=tk.RIGHT, padx=5)
        tk.Button(button_frame, text="Cancel", width=12, command=window.destroy).pack(side=tk.RIGHT)
        item_entry.focus_set()
        window.wait_window()
