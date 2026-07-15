#!/usr/bin/env python3
"""Audit whether blueprint/src/chapters/*.tex is in sync with Algebra0Lean/*.lean.

For each Lean chapter file (e.g. Algebra0Lean/Prelims.lean) this looks at its
matching blueprint chapter (blueprint/src/chapters/prelims.tex, via a
CamelCase -> snake_case name mapping) and cross-references every top-level
`theorem`/`def` against every `\\lean{...}` reference in the blueprint, using
whether the Lean proof still contains `sorry` and whether the blueprint
environment is marked `\\leanok`.

It reports three things, worst first:
  - WRONG:   blueprint says \\leanok but the Lean proof still has `sorry`
             (actively misleading -- fix this first)
  - MISSING: theorem is sorry-free but the blueprint entry lacks \\leanok
  - GAP:     theorem/def is sorry-free (or is a def) but has no blueprint
             entry at all

This is a quick regex-based scan, not a real Lean/LaTeX parser -- treat its
output as "here's what to check by hand", not as ground truth. In
particular it only looks at top-level `theorem`/`def` declarations (not
nested `have`/structure fields), and blueprint dependency status for `def`s
is generally not checked the same way as `theorem`s (see the project's
`\\leanok`-on-defs convention).

Usage: python3 scripts/audit_blueprint_sync.py   (from the repo root)
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "Algebra0Lean"
TEX_DIR = ROOT / "blueprint" / "src" / "chapters"

DECL_RE = re.compile(r"^(theorem|def)\s+([A-Za-z_][A-Za-z0-9_.']*)", re.MULTILINE)
SORRY_RE = re.compile(r"\bsorry\b")
ENV_RE = re.compile(
    r"\\begin\{(proposition|theorem|lemma|corollary|exercise|definition)\}"
    r"(.*?)"
    r"\\end\{\1\}",
    re.DOTALL,
)
LEAN_TAG_RE = re.compile(r"\\lean\{([^}]+)\}")


def camel_to_snake(name: str) -> str:
    return re.sub(r"(?<!^)(?=[A-Z])", "_", name).lower()


def parse_lean(path: Path) -> dict[str, tuple[str, bool]]:
    """Return {decl_name: (kind, has_sorry)} for top-level theorem/def in path."""
    content = path.read_text()
    matches = list(DECL_RE.finditer(content))
    results = {}
    for i, m in enumerate(matches):
        kind, name = m.group(1), m.group(2)
        start = m.start()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(content)
        body = content[start:end]
        results[name] = (kind, bool(SORRY_RE.search(body)))
    return results


def parse_tex(path: Path) -> dict[str, bool]:
    """Return {short_decl_name: has_leanok} for every \\lean{} ref in path."""
    tex = path.read_text()
    lean_to_leanok = {}
    for env in ENV_RE.finditer(tex):
        block = env.group(0)
        has_leanok = "\\leanok" in block
        for lean_tag in LEAN_TAG_RE.finditer(block):
            for full_name in lean_tag.group(1).split(","):
                short_name = full_name.strip().split(".")[-1]
                if short_name:
                    lean_to_leanok[short_name] = has_leanok
    return lean_to_leanok


def audit_chapter(lean_path: Path, tex_path: Path) -> tuple[list, list, list]:
    decls = parse_lean(lean_path)
    lean_to_leanok = parse_tex(tex_path)

    wrong, missing, gap = [], [], []
    for name, (kind, has_sorry) in decls.items():
        in_blueprint = name in lean_to_leanok
        if in_blueprint:
            leanok = lean_to_leanok[name]
            # `def`s are deliberately marked \leanok regardless of `sorry` in
            # internal field values in this project (e.g. preorderCategory),
            # so only `theorem`s are held to the "leanok => no sorry" rule.
            if kind == "theorem" and leanok and has_sorry:
                wrong.append(name)
            elif kind == "theorem" and not has_sorry and not leanok:
                missing.append(name)
        elif kind == "theorem" and not has_sorry:
            gap.append(name)
    return wrong, missing, gap


def main() -> int:
    any_wrong = False
    for lean_path in sorted(LEAN_DIR.glob("*.lean")):
        tex_path = TEX_DIR / f"{camel_to_snake(lean_path.stem)}.tex"
        if not tex_path.exists():
            print(f"# {lean_path.name}: no matching blueprint file ({tex_path.name}), skipping")
            continue

        wrong, missing, gap = audit_chapter(lean_path, tex_path)
        if not (wrong or missing or gap):
            continue

        print(f"# {lean_path.name} <-> {tex_path.relative_to(ROOT)}")
        if wrong:
            any_wrong = True
            print("  WRONG (blueprint says \\leanok, Lean still has `sorry`):")
            for n in wrong:
                print(f"    - {n}")
        if missing:
            print("  MISSING \\leanok (Lean is sorry-free):")
            for n in missing:
                print(f"    - {n}")
        if gap:
            print("  GAP (no blueprint entry at all):")
            for n in gap:
                print(f"    - {n}")
        print()

    return 1 if any_wrong else 0


if __name__ == "__main__":
    sys.exit(main())
