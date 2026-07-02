#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ANNIE end-to-end functional test (headless Tkinter driver).

Drives the real TextAnnotator through every user-facing feature without a
human clicking anything: load, annotate, relations, merge/demerge, remove,
navigation, save/load session + schema, export (CoNLL/JSONL/dictionary),
import, propagation (current-file + dictionary), global search, session-memory
prediction, LLM few-shot prompt building, and the manage-tag/relation dialogs.

Interactive Tk dialogs (filedialog / messagebox / simpledialog / custom
Toplevels) are intercepted with canned answers so the script runs unattended.
A real X display (or xvfb) is required because Tk widgets are exercised for real.

Usage:
    python3 test_annie.py            # run all steps, print report, exit 0/1
    python3 test_annie.py --keep     # keep the temp data dir for inspection

Heavy paths that need optional runtime deps are SKIPped, not failed:
    - HF ensemble AI annotation  (needs torch + downloaded models)
    - LLM agent run              (needs API keys + network)
"""

import os
import sys
import json
import shutil
import tempfile
import traceback
import types

# --- Make `import torch` succeed even when torch isn't installed -------------
# We never run the real HF models here; we only exercise the torch-free paths
# (session-memory prediction, prompt building). Stubbing lets the package import.
try:
    import torch  # noqa: F401
except ModuleNotFoundError:
    torch = types.ModuleType("torch")
    class _Dummy:
        def __getattr__(self, k): return _Dummy()
        def __call__(self, *a, **k): return _Dummy()
    torch.device = lambda *a, **k: _Dummy()
    torch.no_grad = lambda: _Dummy()
    sys.modules["torch"] = torch

import tkinter as tk
from tkinter import filedialog, messagebox, simpledialog

import annie.app as annie_app

# ---------------------------------------------------------------------------
# Test harness
# ---------------------------------------------------------------------------
RESULTS = []  # (name, "PASS"|"FAIL"|"SKIP", detail)


def run_step(name, fn, skip_reason=None):
    if skip_reason:
        RESULTS.append((name, "SKIP", skip_reason))
        print(f"[SKIP] {name}  -- {skip_reason}")
        return
    print(f"\n--- {name} ---")
    try:
        fn()
        RESULTS.append((name, "PASS", ""))
        print(f"[PASS] {name}")
    except Exception as e:
        RESULTS.append((name, "FAIL", f"{type(e).__name__}: {e}"))
        print(f"[FAIL] {name}  -- {type(e).__name__}: {e}")
        traceback.print_exc()


def assert_(cond, msg):
    if not cond:
        raise AssertionError(msg)


# ---------------------------------------------------------------------------
# Temporary sample corpus
# ---------------------------------------------------------------------------
TMP = tempfile.mkdtemp(prefix="annie_test_")
DATA_DIR = os.path.join(TMP, "corpus")
IMPORT_DIR = os.path.join(TMP, "imported")
OUT_DIR = os.path.join(TMP, "out")
for d in (DATA_DIR, IMPORT_DIR, OUT_DIR):
    os.makedirs(d, exist_ok=True)

SAMPLES = {
    "john.txt": "John Smith travelled to London in the year 2020.\nHe works at Acme Corp.",
    "london.txt": "London is a large city. John often visits Paris too.",
    "acme.txt": "Acme Corp is based in Paris. The year 2020 was busy for John.",
}
for fn, content in SAMPLES.items():
    with open(os.path.join(DATA_DIR, fn), "w", encoding="utf-8") as f:
        f.write(content)

# Output paths used by the monkeypatched save dialogs.
SESSION_PATH = os.path.join(OUT_DIR, "test_session.json")
SCHEMA_PATH = os.path.join(OUT_DIR, "test_schema.json")
ANNOT_PATH = os.path.join(OUT_DIR, "annotations.json")
CONLL_PATH = os.path.join(OUT_DIR, "export.conll")
JSONL_PATH = os.path.join(OUT_DIR, "export.jsonl")
DICT_PATH = os.path.join(OUT_DIR, "dictionary.txt")
DICT_IN = os.path.join(OUT_DIR, "dict_in.txt")
with open(DICT_IN, "w", encoding="utf-8") as f:
    f.write("Paris\tLOC\n2020\tDAT\n")
SEARCH_TERM = "John"

# Queues so consecutive dialog calls return different canned paths.
_OPEN_Q = []
_SAVE_Q = []


# ---------------------------------------------------------------------------
# Monkeypatch interactive Tk dialogs
# ---------------------------------------------------------------------------
def _askopenfilename(**kw):
    return _OPEN_Q.pop(0) if _OPEN_Q else ""


def _askopenfilenames(**kw):
    return tuple(_OPEN_Q) if _OPEN_Q else ()


def _asksaveasfilename(**kw):
    return _SAVE_Q.pop(0) if _SAVE_Q else ""


def _askdirectory(**kw):
    return DATA_DIR


# Tk calls these with leading POSITIONAL args (e.g. showinfo("Success", "msg", parent=...)),
# so every stub must accept *args, **kwargs — not just **kwargs.
filedialog.askopenfilename = _askopenfilename
filedialog.askopenfilenames = _askopenfilenames
filedialog.asksaveasfilename = _asksaveasfilename
filedialog.askdirectory = _askdirectory

messagebox.askyesno = lambda *a, **kw: True
messagebox.askokcancel = lambda *a, **kw: True
messagebox.askyesnocancel = lambda *a, **kw: False  # "don't save, just continue"
messagebox.showinfo = lambda *a, **kw: None
messagebox.showwarning = lambda *a, **kw: None
messagebox.showerror = lambda *a, **kw: None
simpledialog.askstring = lambda *a, **kw: SEARCH_TERM


def set_open(path):
    _OPEN_Q.clear()
    _OPEN_Q.append(path)


def set_save(path):
    _SAVE_Q.clear()
    _SAVE_Q.append(path)


# ---------------------------------------------------------------------------
# Dialog-driving helpers (for Toplevels that don't use wait_window)
# ---------------------------------------------------------------------------
def pump():
    app.root.update_idletasks()
    app.root.update()


def find_toplevel(title_substr):
    for w in app.root.winfo_children():
        if isinstance(w, tk.Toplevel):
            t = w.wm_title() or ""
            if title_substr.lower() in t.lower():
                return w
    return None


def find_button(parent, text):
    for c in parent.winfo_children():
        if isinstance(c, tk.Button) and c.cget("text") == text:
            return c
        sub = find_button(c, text) if hasattr(c, "winfo_children") else None
        if sub:
            return sub
    return None


def click_dialog_button(title, text):
    d = find_toplevel(title)
    assert_(d is not None, f"dialog '{title}' not open")
    b = find_button(d, text)
    assert_(b is not None, f"button '{text}' not found in '{title}'")
    b.invoke()
    pump()


def schedule_destroy(title_substr):
    """Destroy a Toplevel (e.g. a wait_window-managed dialog) shortly after."""
    def _d():
        d = find_toplevel(title_substr)
        if d:
            d.destroy()
        pump()
    app.root.after(60, _d)


# ---------------------------------------------------------------------------
# App + selection helper
# ---------------------------------------------------------------------------
app = None  # set in main


def select_text_in_area(word):
    """Set the Tk `sel` tag on the first occurrence of `word` in the text area."""
    app.text_area.config(state=tk.NORMAL)
    start = app.text_area.search(word, "1.0")
    assert_(start, f"'{word}' not found in current text")
    end = f"{start}+{len(word)}c"
    app.text_area.tag_remove(tk.SEL, "1.0", tk.END)
    app.text_area.tag_add(tk.SEL, start, end)
    app.text_area.config(state=tk.DISABLED)
    return start, end


def find_iid_by_text(text):
    for iid in app.entities_tree.get_children():
        vals = app.entities_tree.item(iid)["values"]
        if str(vals[3]) == text:
            return iid
    return None


def entities_in_current():
    return app.annotations.get(app.current_file_path, {}).get("entities", [])


def find_entity(text):
    for e in entities_in_current():
        if e["text"] == text:
            return e
    return None


def file_path_by_name(name):
    for p in app.files_list:
        if os.path.basename(p) == name:
            return p
    return None


def load_by_name(name):
    p = file_path_by_name(name)
    assert_(p is not None, f"file '{name}' not in session")
    app.load_file(app.files_list.index(p))
    pump()


# ---------------------------------------------------------------------------
# Steps
# ---------------------------------------------------------------------------
def step_instantiate():
    global app
    root = tk.Tk()
    root.withdraw()  # no visible window needed
    app = annie_app.TextAnnotator(root)
    # These methods open blocking wait_window Toplevels; bypass them with canned answers
    # so the test runs unattended.
    app._ask_confirm_deletion_with_option = lambda *a, **kw: {"confirmed": True, "option": False}
    app._ask_for_save_directory = lambda initial_dir="": IMPORT_DIR
    pump()
    assert_(app.current_file_path is None, "fresh app should have no file loaded")


def step_load_directory():
    app.load_directory()
    pump()
    assert_(len(app.files_list) == 3, f"expected 3 files, got {len(app.files_list)}")
    assert_(app.current_file_path is not None, "current_file_path should be set")
    # load_directory loads files in sorted order, so the first is acme.txt.
    assert_(os.path.basename(app.current_file_path) == "acme.txt",
            f"first sorted file should be acme.txt, got {os.path.basename(app.current_file_path)}")
    assert_(app.text_area.get("1.0", "end-1c").startswith("Acme"), "text area should show acme.txt")
    app.selection_mode.set("char")  # predictable exact-span annotation


def step_annotate():
    # Annotate on john.txt, the only sample that contains both John and London.
    load_by_name("john.txt")
    app.selected_entity_tag.set("PER")
    select_text_in_area("John")
    app.annotate_selection()
    pump()
    assert_(find_entity("John") is not None, "John entity should be annotated")
    assert_(find_entity("John")["tag"] == "PER", "John tag should be PER")

    app.selected_entity_tag.set("LOC")
    select_text_in_area("London")
    app.annotate_selection()
    pump()
    assert_(find_entity("London") is not None, "London entity should be annotated")
    assert_(find_entity("London")["tag"] == "LOC", "London tag should be LOC")
    assert_(len(entities_in_current()) == 2, f"expected 2 entities, got {len(entities_in_current())}")


def step_relation():
    john = find_entity("John")
    london = find_entity("London")
    app.selected_entity_ids_for_relation = [john["id"], london["id"]]
    app.selected_relation_type.set("spouse_of")
    app.add_relation()
    pump()
    rels = app.annotations[app.current_file_path].get("relations", [])
    assert_(len(rels) == 1, f"expected 1 relation, got {len(rels)}")
    assert_(rels[0]["head_id"] == john["id"] and rels[0]["tail_id"] == london["id"], "relation endpoints wrong")
    assert_(rels[0]["type"] == "spouse_of", "relation type wrong")


def step_save_session():
    set_save(SESSION_PATH)
    app.save_session()
    pump()
    assert_(os.path.isfile(SESSION_PATH), "session file not created")
    data = json.load(open(SESSION_PATH, encoding="utf-8"))
    assert_("files_list" in data and "annotations" in data, "session file missing core keys")
    assert_(len(data["files_list"]) == 3, "session should record 3 files")


def step_load_session():
    set_open(SESSION_PATH)
    app.load_session()
    pump()
    assert_(len(app.files_list) == 3, f"reloaded session should have 3 files, got {len(app.files_list)}")
    ents = entities_in_current()
    assert_(len(ents) == 2, f"reloaded session should have 2 entities, got {len(ents)}")
    rels = app.annotations[app.current_file_path].get("relations", [])
    assert_(len(rels) == 1, f"reloaded session should have 1 relation, got {len(rels)}")


def step_navigate():
    # Current file after load_session is john.txt (index 1).
    app.load_next_file()
    pump()
    assert_(os.path.basename(app.current_file_path) == "london.txt",
            f"next after john.txt should be london.txt, got {os.path.basename(app.current_file_path)}")
    app.load_previous_file()
    pump()
    assert_(os.path.basename(app.current_file_path) == "john.txt",
            f"prev should return to john.txt, got {os.path.basename(app.current_file_path)}")


def step_schema_roundtrip():
    set_save(SCHEMA_PATH)
    app.save_schema()
    pump()
    assert_(os.path.isfile(SCHEMA_PATH), "schema file not created")
    before = json.dumps(app.tag_hierarchy, sort_keys=True)
    set_open(SCHEMA_PATH)
    app.load_schema()
    pump()
    after = json.dumps(app.tag_hierarchy, sort_keys=True)
    assert_(before == after, "schema did not round-trip")


def step_export_conll():
    set_save(CONLL_PATH)
    app.export_annotations()
    pump()
    assert_(os.path.isfile(CONLL_PATH) and os.path.getsize(CONLL_PATH) > 0, "CoNLL export empty/missing")
    content = open(CONLL_PATH, encoding="utf-8").read()
    assert_("B-PER" in content and "B-LOC" in content, "CoNLL export missing expected tags")


def step_export_jsonl():
    set_save(JSONL_PATH)
    app.export_annotations()
    pump()
    assert_(os.path.isfile(JSONL_PATH) and os.path.getsize(JSONL_PATH) > 0, "JSONL export empty/missing")
    line = open(JSONL_PATH, encoding="utf-8").readline()
    doc = json.loads(line)
    assert_("text" in doc and "spans" in doc, "JSONL doc missing text/spans")
    assert_(any(s["label"] == "PER" for s in doc["spans"]), "JSONL missing PER span")


def step_export_dictionary():
    set_save(DICT_PATH)
    app.export_dictionary()
    pump()
    click_dialog_button("Export Dictionary", "Export")
    pump()
    assert_(os.path.isfile(DICT_PATH), "dictionary file not created")
    lines = open(DICT_PATH, encoding="utf-8").read().strip().split("\n")
    found = {l.split("\t")[0] for l in lines if "\t" in l}
    assert_("John" in found and "London" in found, f"dictionary missing John/London: {found}")


def step_propagate_current():
    # Current file is john.txt (John + London); propagate spreads them across all files.
    assert_(os.path.basename(app.current_file_path) == "john.txt", "propagation source should be john.txt")
    app.propagate_annotations()
    pump()
    london_file = file_path_by_name("london.txt")
    ents = [e["text"] for e in app.annotations[london_file].get("entities", [])]
    assert_("John" in ents, f"propagation should add John to london.txt: {ents}")
    assert_("London" in ents, f"propagation should add London to london.txt: {ents}")


def step_propagate_dictionary():
    before = sum(len(d.get("entities", [])) for d in app.annotations.values())
    set_open(DICT_IN)
    app.load_and_propagate_from_dictionary()
    pump()
    click_dialog_button("Target files of propagation", "Propagate")
    pump()
    after = sum(len(d.get("entities", [])) for d in app.annotations.values())
    assert_(after > before, f"dictionary propagation added nothing (before={before}, after={after})")
    has_paris = any(e["text"] == "Paris" for d in app.annotations.values() for e in d.get("entities", []))
    assert_(has_paris, "dictionary propagation should add Paris somewhere")


def step_import():
    files_before = len(app.files_list)
    set_open(CONLL_PATH)
    app.import_annotations()
    pump()
    assert_(len(app.files_list) > files_before, f"import should add files: {files_before} -> {len(app.files_list)}")
    new_files = app.files_list[files_before:]
    assert_(all(os.path.isfile(f) for f in new_files), "imported text files not written to disk")
    has_new_annot = any(len(app.annotations.get(f, {}).get("entities", [])) > 0 for f in new_files)
    assert_(has_new_annot, "imported files should carry parsed annotations")


def step_merge_demerge():
    # import_annotations leaves the first imported file current; switch back to john.txt.
    load_by_name("john.txt")
    john_iid = find_iid_by_text("John")
    london_iid = find_iid_by_text("London")
    assert_(john_iid and london_iid, "could not find John/London tree rows")
    app.entities_tree.selection_set((john_iid, london_iid))
    app.merge_selected_entities()
    pump()
    john = find_entity("John")
    london = find_entity("London")
    assert_(john and london, "entities disappeared after merge")
    assert_(john["id"] == london["id"], "merge should give John and London the same id")

    app.demerge_entity(london)
    pump()
    john = find_entity("John")
    london = find_entity("London")
    assert_(john["id"] != london["id"], "demerge should split ids again")


def step_remove_entity():
    count_before = len(entities_in_current())
    john_iid = find_iid_by_text("John")
    assert_(john_iid, "John row not found for removal")
    app.entities_tree.selection_set((john_iid,))
    app.remove_entity_annotation()
    pump()
    count_after = len(entities_in_current())
    assert_(count_after == count_before - 1, f"remove should drop 1 entity: {count_before} -> {count_after}")
    assert_(find_entity("John") is None, "John should be gone after removal")


def step_search():
    app._search_text_globally(SEARCH_TERM)
    pump()
    dlg = find_toplevel("Search result")
    assert_(dlg is not None, "search results dialog did not open")
    if dlg:
        dlg.destroy()
        pump()


def step_predict_memory():
    # Ensure current file is loaded (file 0).
    app.load_file(0)
    pump()
    before = len(entities_in_current())
    app.predict_from_session_memory()
    pump()
    # Knowledge base built from other files; John/London/Paris/2020 may be predicted.
    after = len(entities_in_current())
    assert_(after >= before, f"memory prediction should not lose entities: {before} -> {after}")


def step_llm_prompt():
    text = app.text_area.get("1.0", "end-1c")
    prompt = app._build_few_shot_prompt(text)
    assert_(isinstance(prompt, str) and len(prompt) > 0, "few-shot prompt should be a non-empty string")
    assert_(text[:20] in prompt or "John" in prompt, "few-shot prompt should embed current text")


def step_manage_dialogs():
    # wait_window-managed: schedule a destroy so the call returns.
    schedule_destroy("Manage Layered Entity Tags")
    app.manage_entity_tags()
    pump()
    schedule_destroy("Manage Relation Types")
    app.manage_relation_types()
    pump()
    # If we got here without exception, the dialogs build and tear down cleanly.


# ---------------------------------------------------------------------------
# AI / LLM runtime steps (skipped without the heavy deps)
# ---------------------------------------------------------------------------
def _torch_real():
    return not isinstance(torch, types.ModuleType)


def step_ai_ensemble_run():
    # _start_ai_annotation_process loads HF pipelines via transformers — not feasible here.
    pass


def step_llm_agent_run():
    # _start_llm_agent needs API keys + network.
    pass


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
def main():
    print("=" * 70)
    print("ANNIE functional test (headless Tkinter driver)")
    print(f"temp dir: {TMP}")
    print(f"display:  {os.environ.get('DISPLAY', '<none>')}")
    print("=" * 70)

    try:
        run_step("instantiate TextAnnotator", step_instantiate)
        run_step("load directory (3 files)", step_load_directory)
        run_step("annotate entities (PER/LOC)", step_annotate)
        run_step("add relation", step_relation)
        run_step("save session", step_save_session)
        run_step("load session (round-trip)", step_load_session)
        run_step("navigate next/prev file", step_navigate)
        run_step("schema save + load", step_schema_roundtrip)
        run_step("export CoNLL", step_export_conll)
        run_step("export spaCy JSONL", step_export_jsonl)
        run_step("export dictionary", step_export_dictionary)
        run_step("propagate current file", step_propagate_current)
        run_step("propagate from dictionary", step_propagate_dictionary)
        run_step("import annotations (CoNLL)", step_import)
        run_step("merge + demerge entities", step_merge_demerge)
        run_step("remove entity", step_remove_entity)
        run_step("global search", step_search)
        run_step("predict from session memory", step_predict_memory)
        run_step("LLM few-shot prompt build", step_llm_prompt)
        run_step("manage-tag/relation dialogs (smoke)", step_manage_dialogs)
        run_step("AI ensemble annotation run",
                 step_ai_ensemble_run,
                 skip_reason="needs torch + HF models (offline, unrunnable here)")
        run_step("LLM agent run",
                 step_llm_agent_run,
                 skip_reason="needs API keys + network")
    finally:
        try:
            app.root.destroy()
        except Exception:
            pass
        keep = "--keep" in sys.argv
        if not keep:
            shutil.rmtree(TMP, ignore_errors=True)
        else:
            print(f"\n(kept temp dir: {TMP})")

    # Report
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    passed = sum(1 for _, s, _ in RESULTS if s == "PASS")
    failed = sum(1 for _, s, _ in RESULTS if s == "FAIL")
    skipped = sum(1 for _, s, _ in RESULTS if s == "SKIP")
    for name, status, detail in RESULTS:
        tag = {"PASS": "OK ", "FAIL": "XX ", "SKIP": "-- "}[status]
        line = f"  [{tag}] {name}"
        if detail:
            line += f"  -- {detail}"
        print(line)
    print("-" * 70)
    print(f"  {passed} passed, {failed} failed, {skipped} skipped")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()