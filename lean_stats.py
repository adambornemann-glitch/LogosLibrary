#!/usr/bin/env python3
"""
lean_stats.py — Library statistics for a Lean 4 project.

Usage:
    python3 lean_stats.py /path/to/LogosLibrary
    python3 lean_stats.py /path/to/LogosLibrary -o stats.md
    python3 lean_stats.py /path/to/LogosLibrary --format txt -o stats.txt

Walks the source tree, ignoring .lake, .ilean, build artifacts, etc.
Counts lines of code (stripping block comments /- ... -/ which can nest),
and tallies declarations: theorem, lemma, def, axiom, structure, class, instance.

Outputs a Markdown or plain-text report to a file (default: library_stats.md).
"""

import argparse
import os
import re
from pathlib import Path
from dataclasses import dataclass, field
from typing import List, Dict, Tuple

# ── Directories and extensions to skip ──────────────────────────────────────

SKIP_DIRS = {
    ".lake", ".git", "build", "lake-packages", "lake-env",
    "__pycache__", "node_modules", ".elan",
}

SKIP_EXTENSIONS = {
    ".ilean", ".olean", ".trace", ".log", ".json", ".toml",
    ".yaml", ".yml", ".lock", ".hash", ".dep",
}

# ── Declaration keywords ────────────────────────────────────────────────────

# We match these at the start of a (comment-stripped) line, allowing leading
# whitespace and optional modifiers like noncomputable / private / protected.
MODIFIERS = r"(?:noncomputable\s+|private\s+|protected\s+|unsafe\s+|partial\s+)*"

DECL_PATTERNS: List[Tuple[str, re.Pattern]] = [
    ("theorem",   re.compile(rf"^\s*{MODIFIERS}theorem\s")),
    ("lemma",     re.compile(rf"^\s*{MODIFIERS}lemma\s")),
    ("def",       re.compile(rf"^\s*{MODIFIERS}def\s")),
    ("axiom",     re.compile(rf"^\s*{MODIFIERS}axiom\s")),
    ("structure",  re.compile(rf"^\s*{MODIFIERS}structure\s")),
    ("class",     re.compile(rf"^\s*{MODIFIERS}class\s")),
    ("instance",  re.compile(rf"^\s*{MODIFIERS}instance\s")),
    ("abbrev",    re.compile(rf"^\s*{MODIFIERS}abbrev\s")),
    ("inductive", re.compile(rf"^\s*{MODIFIERS}inductive\s")),
]


# ── Block comment stripping (handles nesting) ──────────────────────────────

def strip_block_comments(source: str) -> Tuple[str, int]:
    """Remove all /- ... -/ block comments, respecting nesting.
    Returns (stripped_source, number_of_lines_touched_by_block_comments)."""
    result = []
    i = 0
    depth = 0
    n = len(source)
    # Track which lines have any content inside a block comment
    current_line = 0
    lines_in_comments: set = set()
    while i < n:
        if i + 1 < n and source[i] == "/" and source[i + 1] == "-":
            depth += 1
            lines_in_comments.add(current_line)
            i += 2
        elif i + 1 < n and source[i] == "-" and source[i + 1] == "/" and depth > 0:
            depth -= 1
            lines_in_comments.add(current_line)
            i += 2
        elif depth == 0:
            if source[i] == "\n":
                current_line += 1
            result.append(source[i])
            i += 1
        else:
            # Inside a block comment
            lines_in_comments.add(current_line)
            if source[i] == "\n":
                current_line += 1
            i += 1
    return "".join(result), len(lines_in_comments)


# ── Per-file analysis ───────────────────────────────────────────────────────

@dataclass
class FileStats:
    path: str
    raw_lines: int = 0
    code_lines: int = 0          # Non-blank lines after stripping block comments
    blank_lines: int = 0         # Blank lines in stripped output (not inside block comments)
    comment_only_lines: int = 0  # Lines that are ONLY a -- comment after stripping
    block_comment_lines: int = 0 # Lines touched by /- -/ block comments
    decl_counts: Dict[str, int] = field(default_factory=dict)


def analyse_file(filepath: Path, root: Path) -> FileStats:
    rel = str(filepath.relative_to(root))
    try:
        raw = filepath.read_text(encoding="utf-8", errors="replace")
    except Exception:
        return FileStats(path=rel)

    raw_lines = raw.count("\n") + (1 if raw and not raw.endswith("\n") else 0)
    stripped, block_comment_lines = strip_block_comments(raw)
    lines = stripped.split("\n")

    code = 0
    blank = 0
    comment_only = 0
    counts: Dict[str, int] = {name: 0 for name, _ in DECL_PATTERNS}

    for line in lines:
        s = line.strip()
        if not s:
            blank += 1
            continue
        if s.startswith("--"):
            comment_only += 1
            continue
        code += 1
        for name, pat in DECL_PATTERNS:
            if pat.match(line):
                counts[name] += 1
                break  # one declaration per line

    return FileStats(
        path=rel,
        raw_lines=raw_lines,
        code_lines=code,
        blank_lines=blank,
        comment_only_lines=comment_only,
        block_comment_lines=block_comment_lines,
        decl_counts=counts,
    )


# ── Aggregation ─────────────────────────────────────────────────────────────

@dataclass
class LibraryStats:
    root: str
    files: List[FileStats] = field(default_factory=list)

    @property
    def total_raw(self) -> int:
        return sum(f.raw_lines for f in self.files)

    @property
    def total_code(self) -> int:
        return sum(f.code_lines for f in self.files)

    @property
    def total_blank(self) -> int:
        return sum(f.blank_lines for f in self.files)

    @property
    def total_comment_only(self) -> int:
        return sum(f.comment_only_lines for f in self.files)

    @property
    def total_block_comment(self) -> int:
        return sum(f.block_comment_lines for f in self.files)

    def decl_totals(self) -> Dict[str, int]:
        totals: Dict[str, int] = {}
        for f in self.files:
            for k, v in f.decl_counts.items():
                totals[k] = totals.get(k, 0) + v
        return totals


# ── Tree walker ─────────────────────────────────────────────────────────────

def walk_library(root: Path) -> LibraryStats:
    stats = LibraryStats(root=str(root))
    lean_files: List[Path] = []

    for dirpath, dirnames, filenames in os.walk(root):
        # Prune skipped directories in-place
        dirnames[:] = [
            d for d in dirnames
            if d not in SKIP_DIRS and not d.startswith(".")
        ]
        for fname in sorted(filenames):
            fp = Path(dirpath) / fname
            if fp.suffix == ".lean" and fp.suffix not in SKIP_EXTENSIONS:
                lean_files.append(fp)

    lean_files.sort(key=lambda p: str(p.relative_to(root)))

    for fp in lean_files:
        stats.files.append(analyse_file(fp, root))

    return stats


# ── Report formatters ───────────────────────────────────────────────────────

def format_md(stats: LibraryStats) -> str:
    lines: List[str] = []
    w = lines.append

    w(f"# Library Statistics: `{Path(stats.root).name}`\n")
    w(f"**Root:** `{stats.root}`\n")
    w(f"**Files:** {len(stats.files)} `.lean` files\n")

    # ── Summary ──
    w("## Summary\n")
    w(f"| Metric | Count |")
    w(f"|--------|------:|")
    w(f"| Total raw lines | {stats.total_raw:,} |")
    w(f"| Lines of code (no block comments, no blanks, no `--`-only) | {stats.total_code:,} |")
    w(f"| Blank lines | {stats.total_blank:,} |")
    w(f"| Comment-only lines (`--`) | {stats.total_comment_only:,} |")
    w(f"| Lines inside `/- -/` block comments | {stats.total_block_comment:,} |")
    w("")

    # ── Declarations ──
    totals = stats.decl_totals()
    proofs = totals.get("theorem", 0) + totals.get("lemma", 0)
    defs   = totals.get("def", 0) + totals.get("abbrev", 0)
    axioms = totals.get("axiom", 0)
    types  = totals.get("structure", 0) + totals.get("class", 0) + totals.get("inductive", 0)

    w("## Declarations\n")
    w(f"| Kind | Count |")
    w(f"|------|------:|")
    for name, _ in DECL_PATTERNS:
        c = totals.get(name, 0)
        if c > 0:
            w(f"| `{name}` | {c:,} |")
    w(f"| **Proofs (theorem + lemma)** | **{proofs:,}** |")
    w(f"| **Definitions (def + abbrev)** | **{defs:,}** |")
    w(f"| **Axioms** | **{axioms:,}** |")
    w(f"| **Types (structure + class + inductive)** | **{types:,}** |")
    w("")

    # ── File listing ──
    w("## File Listing\n")
    w(f"| # | File | Raw Lines | Code Lines | Thm+Lem | Def | Axiom |")
    w(f"|--:|------|----------:|----------:|--------:|----:|------:|")
    for i, f in enumerate(stats.files, 1):
        p = f.decl_counts
        tl = p.get("theorem", 0) + p.get("lemma", 0)
        df = p.get("def", 0) + p.get("abbrev", 0)
        ax = p.get("axiom", 0)
        w(f"| {i} | `{f.path}` | {f.raw_lines:,} | {f.code_lines:,} | {tl} | {df} | {ax} |")
    w("")

    # ── Top files by code lines ──
    top = sorted(stats.files, key=lambda f: f.code_lines, reverse=True)[:20]
    w("## Top 20 Files by Code Lines\n")
    w(f"| # | File | Code Lines |")
    w(f"|--:|------|----------:|")
    for i, f in enumerate(top, 1):
        w(f"| {i} | `{f.path}` | {f.code_lines:,} |")
    w("")

    # ── Top files by proof count ──
    top_proofs = sorted(
        stats.files,
        key=lambda f: f.decl_counts.get("theorem", 0) + f.decl_counts.get("lemma", 0),
        reverse=True,
    )[:20]
    w("## Top 20 Files by Proof Count (theorem + lemma)\n")
    w(f"| # | File | Proofs |")
    w(f"|--:|------|-------:|")
    for i, f in enumerate(top_proofs, 1):
        c = f.decl_counts.get("theorem", 0) + f.decl_counts.get("lemma", 0)
        if c == 0:
            break
        w(f"| {i} | `{f.path}` | {c} |")
    w("")

    return "\n".join(lines)


def format_txt(stats: LibraryStats) -> str:
    lines: List[str] = []
    w = lines.append

    w(f"LIBRARY STATISTICS: {Path(stats.root).name}")
    w(f"Root: {stats.root}")
    w(f"Files: {len(stats.files)} .lean files")
    w("=" * 72)
    w("")

    w("SUMMARY")
    w("-" * 40)
    w(f"  Total raw lines:          {stats.total_raw:>8,}")
    w(f"  Lines of code:            {stats.total_code:>8,}")
    w(f"  Blank lines:              {stats.total_blank:>8,}")
    w(f"  Comment-only lines (--):  {stats.total_comment_only:>8,}")
    w(f"  Inside /- -/ comments:    {stats.total_block_comment:>8,}")
    w("")

    totals = stats.decl_totals()
    proofs = totals.get("theorem", 0) + totals.get("lemma", 0)
    defs   = totals.get("def", 0) + totals.get("abbrev", 0)
    axioms = totals.get("axiom", 0)
    types  = totals.get("structure", 0) + totals.get("class", 0) + totals.get("inductive", 0)

    w("DECLARATIONS")
    w("-" * 40)
    for name, _ in DECL_PATTERNS:
        c = totals.get(name, 0)
        if c > 0:
            w(f"  {name:<20s} {c:>6,}")
    w(f"  {'--- Proofs (thm+lem)':<20s} {proofs:>6,}")
    w(f"  {'--- Defs (def+abbrev)':<20s} {defs:>6,}")
    w(f"  {'--- Axioms':<20s} {axioms:>6,}")
    w(f"  {'--- Types (str+cls+ind)':<20s} {types:>6,}")
    w("")

    w("FILE LISTING")
    w("-" * 72)
    w(f"  {'#':>4s}  {'Raw':>6s}  {'Code':>6s}  {'T+L':>4s}  {'Def':>4s}  {'Ax':>3s}  Path")
    w(f"  {'':>4s}  {'':>6s}  {'':>6s}  {'':>4s}  {'':>4s}  {'':>3s}  {'':->60s}")
    for i, f in enumerate(stats.files, 1):
        p = f.decl_counts
        tl = p.get("theorem", 0) + p.get("lemma", 0)
        df = p.get("def", 0) + p.get("abbrev", 0)
        ax = p.get("axiom", 0)
        w(f"  {i:>4d}  {f.raw_lines:>6,}  {f.code_lines:>6,}  {tl:>4d}  {df:>4d}  {ax:>3d}  {f.path}")
    w("")

    return "\n".join(lines)


# ── Main ────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Generate statistics for a Lean 4 library.",
        epilog="Example: python3 lean_stats.py ./LogosLibrary -o stats.md",
    )
    parser.add_argument(
        "root",
        help="Root directory of the Lean library (the one with .lean files)",
    )
    parser.add_argument(
        "-o", "--output",
        default=None,
        help="Output file (default: library_stats.md or .txt depending on --format)",
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

    print(f"Scanning {root} ...")
    stats = walk_library(root)
    print(f"Found {len(stats.files)} .lean files.")

    if args.format == "md":
        report = format_md(stats)
        default_name = "library_stats.md"
    else:
        report = format_txt(stats)
        default_name = "library_stats.txt"

    outpath = Path(args.output) if args.output else (root.parent / default_name)
    outpath.write_text(report, encoding="utf-8")
    print(f"Report written to {outpath}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())