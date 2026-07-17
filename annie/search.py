# -*- coding: utf-8 -*-
import tkinter as tk
from tkinter import messagebox
import os
import re

class SearchMixin:
    """Global session text search."""

    def find_text_dialog(self, event=None):
        from tkinter import simpledialog
        search_term = simpledialog.askstring("Global Search", "Search term in entire session:", parent=self.root)
        if search_term: self._search_text_globally(search_term)

    def _search_text_globally(self, term):
        if not self.files_list:
            messagebox.showinfo("Search", "No files loaded in session.", parent=self.root)
            return
        matching_files = []
        term_lower = term.lower()
        self.status_var.set(f"Search in progress: '{term}'...")
        self.root.update()

        for idx, file_path in enumerate(self.files_list):
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    content = f.read().lower()
                    if term_lower in content: matching_files.append((idx, file_path))
            except Exception: continue

        if not matching_files:
            self.status_var.set("Search complete.")
            messagebox.showinfo("Search", f"No results found in the entire session for the following:\n'{term}'", parent=self.root)
            return
        self.status_var.set(f"Found in {len(matching_files)} files.")
        self._show_search_results(term, matching_files)

    def _show_search_results(self, term, matching_files):
        results_window = tk.Toplevel(self.root)
        results_window.title(f"Search result: '{term}'")
        results_window.geometry("500x300")
        results_window.transient(self.root)
        tk.Label(results_window, text=f"{len(matching_files)} found in the document/sentence:").pack(anchor=tk.W, padx=10, pady=5)
        list_frame = tk.Frame(results_window)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        scrollbar = tk.Scrollbar(list_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        results_listbox = tk.Listbox(list_frame, yscrollcommand=scrollbar.set)
        results_listbox.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.config(command=results_listbox.yview)

        for idx, file_path in matching_files:
            display_name = os.path.basename(file_path)
            results_listbox.insert(tk.END, f"[{idx + 1}] {display_name}")

        def on_result_double_click(event):
            selection = results_listbox.curselection()
            if not selection: return
            listbox_idx = selection[0]
            file_idx = matching_files[listbox_idx][0]
            self.load_file(file_idx)
            self._highlight_term_in_current_file(term)

        results_listbox.bind("<Double-Button-1>", on_result_double_click)
        tk.Label(results_window, text="Double-click on the file to open and highlight it.", fg="grey").pack(pady=5)

    def _highlight_term_in_current_file(self, term):
        original_state = self.text_area.cget('state')
        self.text_area.config(state=tk.NORMAL)
        try:
            self.text_area.tag_remove('search_highlight', '1.0', tk.END)
            self.text_area.tag_config('search_highlight', background='yellow', foreground='black')
            start_pos = '1.0'
            first_match = None
            while True:
                start_pos = self.text_area.search(re.escape(term), start_pos, stopindex=tk.END, nocase=True, regexp=True)
                if not start_pos: break
                end_pos = f"{start_pos}+{len(term)}c"
                self.text_area.tag_add('search_highlight', start_pos, end_pos)
                if first_match is None: first_match = start_pos
                start_pos = end_pos
            if first_match:
                self.text_area.see(first_match)
                self.status_var.set(f"Highlights: '{term}'")
        finally:
            if self.text_area.winfo_exists(): self.text_area.config(state=original_state)
