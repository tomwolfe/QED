#!/usr/bin/env python3
"""Wrapper so `opencode run` works when invoked non-interactively (no TTY).

Handles two environment quirks:
  1. opencode ignores the positional message unless it has a PTY -> run under `script`.
  2. opencode silently drops any prompt containing an em-dash (U+2014), en-dash,
     smart quotes, or ellipsis when run without a TTY -> sanitize to ASCII first.
"""
import subprocess
import sys

model = sys.argv[1]
prompt = sys.argv[2]

repl = {
    "\u2014": "-",   # em-dash
    "\u2013": "-",   # en-dash
    "\u2019": "'",   # right single quote
    "\u2018": "'",   # left single quote
    "\u201c": '"',   # left double quote
    "\u201d": '"',   # right double quote
    "\u2026": "...", # ellipsis
    "\u00a0": " ",   # non-breaking space
}
clean = "".join(repl.get(c, c) for c in prompt)

sys.exit(
    subprocess.run(
        ["script", "-q", "/dev/null", "opencode", "run", "-m", model, clean]
    ).returncode
)
