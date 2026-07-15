#!/usr/bin/env python3
"""Audit whether blueprint/src/chapters/*.tex is in sync with Algebra0Lean/*.lean.

For each Lean chapter file (e.g. Algebra0Lean/Prelims.lean) this looks at its
matching blueprint chapter (blueprint/src/chapters/prelims.tex, via a
CamelCase -> snake_case name mapping) and cross-references every top-level
`theorem`/`def` against every `\\lean{...}` reference in the blueprint.

It reports three things, worst first:
  - WRONG:   blueprint says \\leanok but the declaration isn't actually
             sorry-free (actively misleading -- fix this first)
  - MISSING: theorem is sorry-free but the blueprint entry lacks \\leanok
  - GAP:     theorem/def is sorry-free (or is a def) but has no blueprint
             entry at all

By default, "sorry-free" is determined *authoritatively*, by asking Lean
itself: it builds one probe file with `#print axioms <name>` for every
declaration found and runs it via `lake env lean` (so the project must
already be built -- `lake build` first). This catches the case a plain text
search for the word "sorry" cannot: a declaration with no `sorry` in its own
body that still transitively calls something that has one (e.g. a `def`
built from a `Setoid` whose `Equivalence` proof is still `sorry`) --
`#print axioms` reports `sorryAx` in that case because it inspects the
elaborated proof term's full dependency closure, not the source text.
This did happen in this project: Groups.zmodGroup looked complete by a text
scan but transitively depended on equivalence_congMod's `sorry`.

Pass --fast to skip the Lean invocation and fall back to a plain text search
for "sorry" instead (quicker, but can give false confidence -- see above).

`def`s are not held to the "leanok implies fully proved" rule: this project
deliberately marks some `def`s \\leanok even when they depend on `sorry`
inside internal field values or transitively (e.g. preorderCategory), on the
theory that \\leanok for a definition just means "this declaration exists as
stated", not "every proof obligation inside it is discharged". Only
`theorem`s are checked for the WRONG/MISSING categories.

Usage:
  python3 scripts/audit_blueprint_sync.py           (accurate, needs `lake build` first)
  python3 scripts/audit_blueprint_sync.py --fast     (text-only, no build needed)
"""

import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT / "Algebra0Lean"
TEX_DIR = ROOT / "blueprint" / "src" / "chapters"

DECL_RE = re.compile(
    r"^(?:noncomputable\s+|private\s+|protected\s+)*(theorem|def)\s+"
    r"([A-Za-z_][A-Za-z0-9_.']*)",
    re.MULTILINE,
)
NAMESPACE_RE = re.compile(r"^namespace\s+([\w.]+)", re.MULTILINE)
SORRY_RE = re.compile(r"\bsorry\b")
ENV_RE = re.compile(
    r"\\begin\{(proposition|theorem|lemma|corollary|exercise|definition)\}"
    r"(.*?)"
    r"\\end\{\1\}",
    re.DOTALL,
)
LEAN_TAG_RE = re.compile(r"\\lean\{([^}]+)\}")

# Lean wraps long axiom lists across multiple lines, so this must span from
# the declaration name to the next declaration's line (or end of output),
# not just a single line.
PRINT_AXIOMS_BLOCK_RE = re.compile(r"^'([^']+)'.*?(?=^'|\Z)", re.MULTILINE | re.DOTALL)


def camel_to_snake(name: str) -> str:
    return re.sub(r"(?<!^)(?=[A-Z])", "_", name).lower()


def parse_namespace(path: Path) -> str:
    m = NAMESPACE_RE.search(path.read_text())
    return m.group(1) if m else ""


def parse_lean(path: Path) -> dict[str, tuple[str, str, bool]]:
    """Return {short_name: (full_name, kind, has_sorry_text)} for top-level
    theorem/def in path. has_sorry_text is the fast/textual signal only."""
    content = path.read_text()
    namespace = parse_namespace(path)
    matches = list(DECL_RE.finditer(content))
    results = {}
    for i, m in enumerate(matches):
        kind, name = m.group(1), m.group(2)
        start = m.start()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(content)
        body = content[start:end]
        full_name = f"{namespace}.{name}" if namespace else name
        results[name] = (full_name, kind, bool(SORRY_RE.search(body)))
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


def check_axioms(full_names: list[str]) -> dict[str, bool]:
    """Return {full_name: depends_on_sorry} via `#print axioms` in bulk.

    Runs a single `lake env lean` invocation over a generated probe file.
    Requires the project to already be built.
    """
    if not full_names:
        return {}

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", delete=False
    ) as f:
        f.write("import Algebra0Lean\n\n")
        for name in full_names:
            f.write(f"#print axioms {name}\n")
        probe_path = Path(f.name)

    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(probe_path)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            timeout=300,
        )
    finally:
        probe_path.unlink(missing_ok=True)

    output = result.stdout + result.stderr
    status = {}
    for block_match in PRINT_AXIOMS_BLOCK_RE.finditer(output):
        name = block_match.group(1)
        status[name] = "sorryAx" in block_match.group(0)
    return status


def audit_chapter(
    lean_path: Path, tex_path: Path, axiom_status: dict[str, bool] | None
) -> tuple[list, list, list]:
    decls = parse_lean(lean_path)
    lean_to_leanok = parse_tex(tex_path)

    wrong, missing, gap = [], [], []
    for name, (full_name, kind, has_sorry_text) in decls.items():
        if axiom_status is not None and full_name in axiom_status:
            has_sorry = axiom_status[full_name]
        else:
            has_sorry = has_sorry_text
        in_blueprint = name in lean_to_leanok
        if in_blueprint:
            leanok = lean_to_leanok[name]
            # `def`s are deliberately marked \leanok regardless of `sorry`
            # (direct or transitive) in this project (e.g. preorderCategory),
            # so only `theorem`s are held to the "leanok => no sorry" rule.
            if kind == "theorem" and leanok and has_sorry:
                wrong.append(name)
            elif kind == "theorem" and not has_sorry and not leanok:
                missing.append(name)
        elif kind == "theorem" and not has_sorry:
            gap.append(name)
    return wrong, missing, gap


def main() -> int:
    fast = "--fast" in sys.argv[1:]

    lean_paths = sorted(LEAN_DIR.glob("*.lean"))
    chapter_pairs = []
    for lean_path in lean_paths:
        tex_path = TEX_DIR / f"{camel_to_snake(lean_path.stem)}.tex"
        if not tex_path.exists():
            print(f"# {lean_path.name}: no matching blueprint file ({tex_path.name}), skipping")
            continue
        chapter_pairs.append((lean_path, tex_path))

    axiom_status = None
    if not fast:
        all_full_names = []
        for lean_path, _ in chapter_pairs:
            for full_name, _kind, _has_sorry in parse_lean(lean_path).values():
                all_full_names.append(full_name)
        print(f"Checking {len(all_full_names)} declarations via `#print axioms` "
              f"(requires the project to be built; pass --fast to skip)...",
              file=sys.stderr)
        axiom_status = check_axioms(all_full_names)

    any_wrong = False
    for lean_path, tex_path in chapter_pairs:
        wrong, missing, gap = audit_chapter(lean_path, tex_path, axiom_status)
        if not (wrong or missing or gap):
            continue

        print(f"# {lean_path.name} <-> {tex_path.relative_to(ROOT)}")
        if wrong:
            any_wrong = True
            print("  WRONG (blueprint says \\leanok, but not actually sorry-free):")
            for n in wrong:
                print(f"    - {n}")
        if missing:
            print("  MISSING \\leanok (sorry-free):")
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
