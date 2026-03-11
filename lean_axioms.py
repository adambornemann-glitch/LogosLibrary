#!/usr/bin/env python3
"""
lean_axioms.py — Axiom audit for a Lean 4 library.

Usage:
    python3 lean_axioms.py /path/to/LogosLibrary
    python3 lean_axioms.py /path/to/LogosLibrary -o axiom_audit.md
    python3 lean_axioms.py /path/to/LogosLibrary --format txt -o axiom_audit.txt

    python3 lean_axioms.py LogosLibrary -o axiom_audit.md

Finds every `axiom` declaration, extracts its name and signature,
and reports them grouped by directory with summary statistics.
"""

import argparse
import os
import re
from pathlib import Path
from dataclasses import dataclass, field
from typing import List, Dict, Tuple
from collections import defaultdict

# ── Skip rules (same as lean_stats.py) ──────────────────────────────────────

SKIP_DIRS = {
    ".lake", ".git", "build", "lake-packages", "lake-env",
    "__pycache__", "node_modules", ".elan",
}

SKIP_EXTENSIONS = {
    ".ilean", ".olean", ".trace", ".log", ".json", ".toml",
    ".yaml", ".yml", ".lock", ".hash", ".dep",
}

# ── Block comment stripping (handles nesting) ──────────────────────────────

def strip_block_comments(source: str) -> str:
    """Remove all /- ... -/ block comments, respecting nesting."""
    result = []
    i = 0
    depth = 0
    n = len(source)
    while i < n:
        if i + 1 < n and source[i] == "/" and source[i + 1] == "-":
            depth += 1
            i += 2
        elif i + 1 < n and source[i] == "-" and source[i + 1] == "/" and depth > 0:
            depth -= 1
            i += 2
        elif depth == 0:
            result.append(source[i])
            i += 1
        else:
            # Preserve newlines for line number tracking
            if source[i] == "\n":
                result.append("\n")
            i += 1
    return "".join(result)


# ── Axiom extraction ────────────────────────────────────────────────────────

MODIFIERS = r"(?:noncomputable\s+|private\s+|protected\s+|unsafe\s+|partial\s+)*"
AXIOM_DECL = re.compile(
    rf"^\s*{MODIFIERS}axiom\s+(\S+)",
    re.MULTILINE,
)


@dataclass
class AxiomInfo:
    name: str           # The axiom identifier
    file: str           # Relative path
    line: int           # Line number in the ORIGINAL source (1-indexed)
    signature: str      # The full declaration (trimmed, up to next decl or blank)
    namespace: str      # Enclosing namespace, if any


def find_axioms_in_file(filepath: Path, root: Path) -> List[AxiomInfo]:
    """Extract all axiom declarations from a single .lean file."""
    rel = str(filepath.relative_to(root))
    try:
        raw = filepath.read_text(encoding="utf-8", errors="replace")
    except Exception:
        return []

    raw_lines = raw.split("\n")

    # Build a map: for each line in the stripped source, what's the
    # corresponding line in the original? We do this by stripping comments
    # but tracking original line numbers.
    stripped = strip_block_comments(raw)
    stripped_lines = stripped.split("\n")

    # Build original-line-number mapping:
    # Walk the raw source and stripped source in parallel via newline counting.
    # Since strip_block_comments preserves newlines, line counts match.
    # But we need the ORIGINAL line numbers for lines that contain axioms.
    # Since we preserve \n in block comments, stripped line N corresponds to raw line N.

    # Track namespaces
    current_namespaces: List[str] = []
    ns_open = re.compile(r"^\s*namespace\s+(\S+)")
    ns_end = re.compile(r"^\s*end\s+(\S+)")

    axioms: List[AxiomInfo] = []

    for line_idx, line in enumerate(stripped_lines):
        # Track namespace
        m_open = ns_open.match(line)
        if m_open:
            current_namespaces.append(m_open.group(1))
            continue
        m_end = ns_end.match(line)
        if m_end:
            # Pop matching namespace (or closest)
            ns_name = m_end.group(1)
            for i in range(len(current_namespaces) - 1, -1, -1):
                if current_namespaces[i] == ns_name:
                    current_namespaces.pop(i)
                    break
            continue

        # Check for axiom
        s = line.strip()
        if s.startswith("--"):
            continue

        m_axiom = AXIOM_DECL.match(line)
        if m_axiom:
            axiom_name = m_axiom.group(1)

            # Extract the full signature: collect lines until we hit a blank
            # line, another top-level declaration, or end of file.
            sig_lines = [stripped_lines[line_idx].strip()]
            j = line_idx + 1
            while j < len(stripped_lines):
                next_line = stripped_lines[j].strip()
                if not next_line:
                    break
                # Stop if we hit another top-level declaration
                if re.match(rf"^\s*{MODIFIERS}(theorem|lemma|def|axiom|structure|class|instance|abbrev|inductive)\s", stripped_lines[j]):
                    break
                sig_lines.append(next_line)
                j += 1

            signature = " ".join(sig_lines)
            # Truncate very long signatures
            if len(signature) > 300:
                signature = signature[:297] + "..."

            ns = ".".join(current_namespaces) if current_namespaces else "(root)"

            axioms.append(AxiomInfo(
                name=axiom_name,
                file=rel,
                line=line_idx + 1,  # 1-indexed
                signature=signature,
                namespace=ns,
            ))

    return axioms


# ── Walk the tree ───────────────────────────────────────────────────────────

def walk_library(root: Path) -> List[AxiomInfo]:
    all_axioms: List[AxiomInfo] = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [
            d for d in dirnames
            if d not in SKIP_DIRS and not d.startswith(".")
        ]
        for fname in sorted(filenames):
            fp = Path(dirpath) / fname
            if fp.suffix == ".lean" and fp.suffix not in SKIP_EXTENSIONS:
                all_axioms.extend(find_axioms_in_file(fp, root))
    all_axioms.sort(key=lambda a: (a.file, a.line))
    return all_axioms


# ── Grouping helpers ────────────────────────────────────────────────────────

def group_by_directory(axioms: List[AxiomInfo], depth: int = 2) -> Dict[str, List[AxiomInfo]]:
    """Group axioms by directory path, truncated to `depth` levels."""
    groups: Dict[str, List[AxiomInfo]] = defaultdict(list)
    for ax in axioms:
        parts = Path(ax.file).parts[:-1]  # drop filename
        key = "/".join(parts[:depth]) if parts else "(root)"
        groups[key].append(ax)
    return dict(sorted(groups.items()))


def group_by_file(axioms: List[AxiomInfo]) -> Dict[str, List[AxiomInfo]]:
    groups: Dict[str, List[AxiomInfo]] = defaultdict(list)
    for ax in axioms:
        groups[ax.file].append(ax)
    return dict(sorted(groups.items()))


def group_by_namespace(axioms: List[AxiomInfo]) -> Dict[str, List[AxiomInfo]]:
    groups: Dict[str, List[AxiomInfo]] = defaultdict(list)
    for ax in axioms:
        groups[ax.namespace].append(ax)
    return dict(sorted(groups.items()))


# ── Formatters ──────────────────────────────────────────────────────────────

def format_md(axioms: List[AxiomInfo], root: str) -> str:
    lines: List[str] = []
    w = lines.append

    w(f"# Axiom Audit: `{Path(root).name}`\n")
    w(f"**Total axioms:** {len(axioms)}\n")

    # ── By directory ──
    by_dir = group_by_directory(axioms, depth=2)
    w("## Axioms by Directory\n")
    w("| Directory | Count |")
    w("|-----------|------:|")
    for d, axs in by_dir.items():
        w(f"| `{d}` | {len(axs)} |")
    w("")

    # ── By file ──
    by_file = group_by_file(axioms)
    w("## Axioms by File\n")
    w("| File | Count | Axiom Names |")
    w("|------|------:|-------------|")
    for f, axs in by_file.items():
        names = ", ".join(f"`{a.name}`" for a in axs)
        w(f"| `{f}` | {len(axs)} | {names} |")
    w("")

    # ── Full catalogue ──
    w("## Full Axiom Catalogue\n")
    current_dir = None
    for ax in axioms:
        d = str(Path(ax.file).parent)
        if d != current_dir:
            current_dir = d
            w(f"### `{d}/`\n")

        w(f"**`{ax.name}`** — `{ax.file}:{ax.line}`\n")
        # Show signature in a code block, but keep it compact
        sig = ax.signature
        w(f"```lean")
        w(f"{sig}")
        w(f"```\n")

    # ── By namespace ──
    by_ns = group_by_namespace(axioms)
    w("## Axioms by Namespace\n")
    w("| Namespace | Count | Axiom Names |")
    w("|-----------|------:|-------------|")
    for ns, axs in by_ns.items():
        names = ", ".join(f"`{a.name}`" for a in axs)
        w(f"| `{ns}` | {len(axs)} | {names} |")
    w("")

    return "\n".join(lines)


def format_txt(axioms: List[AxiomInfo], root: str) -> str:
    lines: List[str] = []
    w = lines.append

    w(f"AXIOM AUDIT: {Path(root).name}")
    w(f"Total axioms: {len(axioms)}")
    w("=" * 72)
    w("")

    # ── By directory ──
    by_dir = group_by_directory(axioms, depth=2)
    w("BY DIRECTORY")
    w("-" * 40)
    for d, axs in by_dir.items():
        w(f"  {d:<50s} {len(axs):>4d}")
    w("")

    # ── By file ──
    by_file = group_by_file(axioms)
    w("BY FILE")
    w("-" * 72)
    for f, axs in by_file.items():
        w(f"  {f}  ({len(axs)})")
        for ax in axs:
            w(f"    L{ax.line:<5d} {ax.name}")
    w("")

    # ── Full catalogue ──
    w("FULL CATALOGUE")
    w("-" * 72)
    current_dir = None
    for ax in axioms:
        d = str(Path(ax.file).parent)
        if d != current_dir:
            current_dir = d
            w(f"\n  [{d}/]")
            w("")

        w(f"  {ax.name}")
        w(f"    File: {ax.file}:{ax.line}")
        w(f"    Namespace: {ax.namespace}")
        sig = ax.signature
        if len(sig) > 120:
            sig = sig[:117] + "..."
        w(f"    Sig:  {sig}")
        w("")

    return "\n".join(lines)


# ── Main ────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Audit axiom declarations in a Lean 4 library.",
        epilog="Example: python3 lean_axioms.py ./LogosLibrary -o axiom_audit.md",
    )
    parser.add_argument(
        "root",
        help="Root directory of the Lean library",
    )
    parser.add_argument(
        "-o", "--output",
        default=None,
        help="Output file (default: axiom_audit.md or .txt)",
    )
    parser.add_argument(
        "--format",
        choices=["md", "txt"],
        default="md",
        help="Output format (default: md)",
    )

    args = parser.parse_args()
    root = Path(args.root).resolve()

    if not root.is_dir():
        print(f"Error: {root} is not a directory.")
        return 1

    print(f"Scanning {root} for axioms ...")
    axioms = walk_library(root)
    print(f"Found {len(axioms)} axioms.")

    if args.format == "md":
        report = format_md(axioms, str(root))
        default_name = "axiom_audit.md"
    else:
        report = format_txt(axioms, str(root))
        default_name = "axiom_audit.txt"

    outpath = Path(args.output) if args.output else (root.parent / default_name)
    outpath.write_text(report, encoding="utf-8")
    print(f"Report written to {outpath}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())