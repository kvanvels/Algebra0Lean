#!/usr/bin/env python3
"""Generate the Exercises/ library from the Algebra0Lean/ solutions.

For every chapter file, theorem proofs are replaced by `sorry` while
definitions, structures, docstrings, and section plumbing are kept, so
each generated file states the book's results as exercises for the
reader. Modeled on Mathematics in Lean's solutions/exercises split.

A theorem keeps its solution if its signature line contains the marker
comment `-- mk_exercises: keep`.

Usage: python3 scripts/mk_exercises.py   (from the repo root)
"""

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "Algebra0Lean"
DST = ROOT / "Exercises"

DECL_RE = re.compile(r"^(theorem|lemma|example)\b")
KEEP_MARKER = "-- mk_exercises: keep"

HEADER = (
    "/- Auto-generated from `Algebra0Lean/{name}` by `scripts/mk_exercises.py`.\n"
    "   Do not edit by hand: fill in the `sorry`s in your own copy, and\n"
    "   compare with `Algebra0Lean/{name}` for the solutions. -/\n\n"
)


def strip_proofs(text: str) -> str:
    lines = text.split("\n")
    out = []
    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        if not DECL_RE.match(line):
            out.append(line)
            i += 1
            continue
        # Copy signature lines until the one ending in `:=` or `:= by`,
        # which starts the proof.
        keep = False
        sig_end = None
        j = i
        while j < n:
            sig_line = lines[j]
            if KEEP_MARKER in sig_line:
                keep = True
            stripped = sig_line.rstrip()
            if stripped.endswith(":= by") or stripped.endswith(":="):
                sig_end = j
                break
            # A `:=` mid-line (proof on the same line) also ends the
            # signature; conservative: treat any line containing `:=`
            # as the boundary.
            if ":=" in stripped:
                sig_end = j
                break
            j += 1
        if sig_end is None:
            # Malformed / statement without proof; copy verbatim.
            out.append(line)
            i += 1
            continue
        # Find the end of the proof: the next non-blank line at column 0.
        k = sig_end + 1
        while k < n:
            nxt = lines[k]
            if nxt.strip() and not nxt[0].isspace():
                break
            k += 1
        if keep:
            out.extend(lines[i : k])
        else:
            sig = lines[i : sig_end + 1]
            last = sig[-1].rstrip()
            # Normalize the proof opener to `:= by` and insert `sorry`.
            if last.endswith(":= by"):
                sig[-1] = last
                out.extend(sig)
                out.append("  sorry")
            elif last.endswith(":="):
                sig[-1] = last
                out.extend(sig)
                out.append("  sorry")
            else:
                # `:=` mid-line with an inline proof: cut at `:=`.
                cut = last.index(":=") + len(":=")
                sig[-1] = last[:cut]
                out.extend(sig)
                out.append("  sorry")
            out.append("")
        i = k
    # Collapse runs of blank lines left behind by stripped proofs.
    collapsed = []
    blanks = 0
    for line in out:
        if line.strip() == "":
            blanks += 1
            if blanks <= 1:
                collapsed.append("")
        else:
            blanks = 0
            collapsed.append(line)
    return "\n".join(collapsed).rstrip() + "\n"


def main() -> None:
    DST.mkdir(exist_ok=True)
    modules = []
    for src in sorted(SRC.glob("*.lean")):
        name = src.name
        if not name[0].isalpha():  # Emacs lock/backup files
            continue
        text = src.read_text()
        # Re-namespace so exercises never collide with the solutions
        # (e.g. when a tool imports both libraries into one environment).
        text = re.sub(
            r"^(namespace|end) Algebra0Lean\.",
            r"\1 Exercises.",
            text,
            flags=re.MULTILINE,
        )
        gen = HEADER.format(name=name) + strip_proofs(text)
        (DST / name).write_text(gen)
        modules.append(name.removesuffix(".lean"))
        print(f"wrote Exercises/{name}")
    root = ROOT / "Exercises.lean"
    root.write_text(
        "\n".join(f"import Exercises.{m}" for m in modules) + "\n"
    )
    print("wrote Exercises.lean")


if __name__ == "__main__":
    main()
