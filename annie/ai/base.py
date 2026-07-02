# -*- coding: utf-8 -*-
import re
import queue
import math
from collections import Counter

class AIBaseMixin:
    """Shared AI/LLM helpers: status queue + retrieval."""

    def _update_status_threadsafe(self, message):
        self.ai_status_queue.put(message)

    def _process_queue(self):
        try:
            while True:
                message = self.ai_status_queue.get_nowait()

                # Check for explicit DONE signal to stop progress bar
                if message.startswith("DONE|"):
                    self.status_var.set(message.split("|", 1)[1])
                    self.progress_bar.stop()
                    try: self.settings_menu.entryconfig("Pre-annotate with Hybrid AI...", state="normal")
                    except: pass
                else:
                    self.status_var.set(message)
                    self.progress_bar.start()

                self.root.update()
        except queue.Empty: pass
        self.root.after(100, self._process_queue)

    def _retrieve_similar_examples(self, query_text, top_k):
        """
        RAG: TF-IDF
        """
        corpus_docs = []
        corpus_data = []

        for fp, data in self.annotations.items():
            if fp == self.current_file_path: continue
            entities = data.get('entities', [])
            if not entities: continue

            try:
                with open(fp, 'r', encoding='utf-8') as f:
                    text = f.read()
            except Exception:
                continue

            corpus_docs.append(text)
            corpus_data.append((text, entities))

        if not corpus_docs:
            return []

        def tokenize(t):
            return re.findall(r'\w+', t.lower())

        corpus_tokens = [tokenize(doc) for doc in corpus_docs]
        query_tokens = tokenize(query_text)

        if not query_tokens:
            return corpus_data[:top_k]

        N = len(corpus_tokens)
        df = Counter()
        for tokens in corpus_tokens:
            for w in set(tokens):
                df[w] += 1

        # idf(t) = log [ (1 + n) / (1 + df(d, t)) ] + 1
        idf = {w: math.log((1 + N) / (1 + df[w])) + 1 for w in df}

        def get_tfidf_vector(tokens):
            tf = Counter(tokens)
            total_words = len(tokens) if tokens else 1
            vec = {}
            for w, count in tf.items():
                w_idf = idf.get(w, math.log((1 + N) / 1) + 1)  # Unknown word in query
                vec[w] = (count / total_words) * w_idf
            return vec

        query_vec = get_tfidf_vector(query_tokens)
        corpus_vecs = [get_tfidf_vector(tokens) for tokens in corpus_tokens]

        def cosine_sim(v1, v2):
            intersection = set(v1.keys()) & set(v2.keys())
            dot_product = sum(v1[w] * v2[w] for w in intersection)
            norm_v1 = math.sqrt(sum(val**2 for val in v1.values()))
            norm_v2 = math.sqrt(sum(val**2 for val in v2.values()))
            if norm_v1 == 0 or norm_v2 == 0: return 0.0
            return dot_product / (norm_v1 * norm_v2)

        scores = [(cosine_sim(query_vec, cv), data) for cv, data in zip(corpus_vecs, corpus_data)]
        scores.sort(key=lambda x: x[0], reverse=True)

        return [data for score, data in scores[:top_k]]
