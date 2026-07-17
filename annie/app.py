# -*- coding: utf-8 -*-
"""ANNIE application: combines all mixin modules into TextAnnotator + main() entry point."""

import tkinter as tk
from tkinter import ttk
import itertools
import queue

from annie.constants import SESSION_FILE_VERSION
from annie.core import CoreMixin
from annie.ui_state import UIStateMixin
from annie.ui.menu import MenuMixin
from annie.ui.layout import LayoutMixin
from annie.ui.bindings import BindingsMixin
from annie.io.files import FilesMixin
from annie.io.session import SessionMixin
from annie.io.api_keys import ApiKeysMixin
from annie.io.export import ExportMixin
from annie.io.import_parser import ImportMixin
from annie.annotation.core import AnnotationMixin
from annie.annotation.propagation import PropagationMixin
from annie.annotation.manage import ManageMixin
from annie.ai.base import AIBaseMixin
from annie.ai.ensemble import AIMixin
from annie.ai.llm import LLMMixin
from annie.search import SearchMixin


class TextAnnotator(
    CoreMixin, UIStateMixin, BindingsMixin, MenuMixin, LayoutMixin,
    FilesMixin, SessionMixin, ApiKeysMixin, ExportMixin, ImportMixin,
    AnnotationMixin, PropagationMixin, ManageMixin,
    AIBaseMixin, AIMixin, LLMMixin, SearchMixin,
):
    """Handles UI creation, file loading, annotation logic, and saving."""

    def __init__(self, root_window):
        self.root = root_window
        self.root.title("ANNIE - Annotation Interface")
        self.root.geometry("1200x850")

        # --- Core Data ---
        self.current_file_path = None
        self.files_list = []
        self.current_file_index = -1
        self.annotations = {}
        self.session_save_path = None

        # --- Optimized Data Structures ---
        self.line_start_offsets = [0]
        self._entity_lookup_map = {}

        # --- Entity Tagging Configuration (Hierarchical) ---
        self.tag_hierarchy = {
            "CORE Layer": ["PER", "LOC", "INS", "DAT", "TIM"],
            "ANALYTICAL Layer": ["TITLE", "REL", "TAX", "MEA", "COM", "EST", "MON", "NUM", "LEG", "NAT"],
            "SPAN Layer": ["ACTOR", "PROP", "TRANS"]
        }
        self.tag_active_states = {tag: True for layer in self.tag_hierarchy.values() for tag in layer}
        self.tag_propagation_states = {tag: True for layer in self.tag_hierarchy.values() for tag in layer}
        self.tag_visible_states = {tag: True for layer in self.tag_hierarchy.values() for tag in layer}

        self.entity_tags = []
        self._sync_flat_tags()
        self.selected_entity_tag = tk.StringVar(value=self.get_active_tags()[0] if self.get_active_tags() else "")
        self.extend_to_word = tk.BooleanVar(value=False)
        self.allow_multilabel_overlap = tk.BooleanVar(value=True)

        # --- Relation Tagging Configuration ---
        self.relation_types = ["spouse_of", "works_at", "located_in", "born_on", "produces"]
        self.selected_relation_type = tk.StringVar(value=self.relation_types[0] if self.relation_types else "")
        self.selection_mode = tk.StringVar(value="word")

        # --- UI State ---
        self.selected_entity_ids_for_relation = []
        self._entity_id_to_tree_iids = {}
        self._click_time = 0
        self._click_pos = (0, 0)
        self._is_deleting = False
        self._is_annotating_ai = False
        self._just_double_clicked = False
        self.last_used_ai_models = []
        self.current_ai_models = []

        # --- AI Settings State ---
        self.ai_min_conf = 0.90
        self.ai_max_conf = 1.00
        self.ai_label_mapping = {}

        self.llm_provider = "Anthropic (Claude)"
        # --- LLM Agent State ---
        self.llm_models = {
            "OpenAI": "gpt-4o-mini",
            "Anthropic (Claude)": "claude-sonnet-4-6",
            "Together AI": "meta-llama/Meta-Llama-3.1-8B-Instruct-Turbo",
            "Hugging Face": "HuggingFaceH4/zephyr-7b-alpha"
        }
        self.llm_model = self.llm_models[self.llm_provider]

        self._load_api_keys()
        self.llm_few_shot_count = 3

        # --- Sort Tracking ---
        self.entities_sort_column = None
        self.entities_sort_reverse = False
        self.relations_sort_column = None
        self.relations_sort_reverse = False

        # --- Colors ---
        self.tag_colors = {
            "PER": "#ffcccc", "LOC": "#ccccff", "INS": "#ccffcc",
            "DAT": "#ffffcc", "TITLE": "#ccffff"
        }
        self.color_cycle = itertools.cycle([
            "#e6e6fa", "#ffe4e1", "#f0fff0", "#fffacd", "#add8e6",
            "#f5f5dc", "#d3ffd3", "#fafad2", "#ffebcd", "#e0ffff"
        ])
        self._ensure_default_colors()

        # --- Status Bar and Progress Bar Setup ---
        self.status_var = tk.StringVar(value="Ready. Open a directory or load a session.")
        status_frame = tk.Frame(self.root, bd=1, relief=tk.SUNKEN)
        status_frame.pack(side=tk.BOTTOM, fill=tk.X)
        status_inner_frame = tk.Frame(status_frame, height=25)
        status_inner_frame.pack(fill=tk.X, expand=True)
        status_inner_frame.pack_propagate(False)
        status_label = tk.Label(status_inner_frame, textvariable=self.status_var, anchor=tk.W, background='gray85')
        status_label.pack(side=tk.LEFT, padx=5, pady=2, fill=tk.X, expand=True)
        self.progress_bar = ttk.Progressbar(status_inner_frame, orient='horizontal', mode='indeterminate', length=200)
        self.progress_bar.pack(side=tk.RIGHT, padx=5, pady=2, fill=tk.X, expand=False)
        self.progress_bar.stop()
        self.ai_status_queue = queue.Queue()
        self._process_queue()

        # --- Build UI ---
        self.create_menu()
        self.create_layout()

        # --- Initial UI Setup ---
        self._update_entity_tag_combobox()
        self._update_relation_type_combobox()
        self._configure_text_tags()
        self._configure_treeview_tags()
        self._update_button_states()

        # --- Bind Hotkeys ---
        for i in range(10):
            self.root.bind(str(i), self._on_hotkey_press)
        # AI
        self.root.bind('a', lambda event: self.run_ai_annotation_from_hotkey())
        # Generative
        self.root.bind('g', lambda event: self.run_llm_agent_from_hotkey())
        self.root.protocol("WM_DELETE_WINDOW", self._on_closing)
        self.root.bind('<Control-f>', self.find_text_dialog)

def main():
    root = tk.Tk()
    try:
        style = ttk.Style()
        themes = style.theme_names()
        preferred_themes = ['clam', 'alt', 'vista', 'xpnative']
        current_theme = style.theme_use()
        if current_theme not in preferred_themes:
            for t in preferred_themes:
                if t in themes:
                    try:
                        style.theme_use(t)
                        break
                    except tk.TclError: continue
            else:
                if 'default' in themes : style.theme_use('default')
    except tk.TclError: print("ttk themes not available or failed to apply.")
    app = TextAnnotator(root)
    root.mainloop()

if __name__ == "__main__":
    main()
