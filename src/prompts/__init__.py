"""Prompt templates, stored as Markdown rather than Python string literals.

Each ``*.md`` file in this directory is a template with ``{placeholder}``
fields. :func:`render` fills them in and fails loudly on a missing field, so a
prompt change never silently produces a half-filled prompt.

Keeping prompts as files means they can be diffed, reviewed, and shipped as
artifacts alongside the results they produced.
"""
from __future__ import annotations

import string
from pathlib import Path

_DIR = Path(__file__).parent


class _Strict(string.Formatter):
    def get_value(self, key, args, kwargs):
        if isinstance(key, str) and key not in kwargs:
            raise KeyError(f"prompt placeholder '{{{key}}}' was not supplied")
        return super().get_value(key, args, kwargs)


def load(name: str) -> str:
    path = _DIR / f"{name}.md"
    if not path.exists():
        raise FileNotFoundError(f"no prompt template: {path}")
    return path.read_text()


def render(name: str, **fields) -> str:
    """Render ``<name>.md`` with ``fields``; unknown placeholders raise."""
    return _Strict().vformat(load(name), (), fields)


def available() -> list[str]:
    return sorted(p.stem for p in _DIR.glob("*.md"))
