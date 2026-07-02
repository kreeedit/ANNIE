# -*- coding: utf-8 -*-
from pathlib import Path

class ApiKeysMixin:
    """Persisted API key load/save."""

    def _load_api_keys(self):
        self.hf_api_key = ""
        self.claude_api_key = ""
        self.openai_api_key = ""
        self.together_api_key = ""

        env_path = Path(".env")
        if env_path.exists():
            with open(env_path, "r", encoding="utf-8") as f:
                for line in f:
                    line = line.strip()
                    if not line or line.startswith("#"): continue
                    if "=" in line:
                        key, val = line.split("=", 1)
                        key, val = key.strip(), val.strip()
                        if key == "HF_API_KEY": self.hf_api_key = val
                        elif key == "CLAUDE_API_KEY": self.claude_api_key = val
                        elif key == "OPENAI_API_KEY": self.openai_api_key = val
                        elif key == "TOGETHER_API_KEY": self.together_api_key = val

    def _save_api_keys(self):
        env_path = Path(".env")
        existing_lines = []
        if env_path.exists():
            with open(env_path, "r", encoding="utf-8") as f:
                existing_lines = f.readlines()

        keys_to_save = {
            "HF_API_KEY": self.hf_api_key,
            "CLAUDE_API_KEY": self.claude_api_key,
            "OPENAI_API_KEY": self.openai_api_key,
            "TOGETHER_API_KEY": self.together_api_key
        }

        new_lines = []
        for line in existing_lines:
            stripped = line.strip()
            if stripped and not stripped.startswith("#") and "=" in stripped:
                k, _ = stripped.split("=", 1)
                k = k.strip()
                if k in keys_to_save:
                    if keys_to_save[k]:
                        new_lines.append(f"{k}={keys_to_save[k]}\n")
                    del keys_to_save[k]
                else:
                    new_lines.append(line)
            else:
                new_lines.append(line)

        for k, v in keys_to_save.items():
            if v:
                new_lines.append(f"{k}={v}\n")

        with open(env_path, "w", encoding="utf-8") as f:
            f.writelines(new_lines)
