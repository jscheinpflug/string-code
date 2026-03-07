#!/usr/bin/env python3
"""
Convert VSCode-style .wlnb notebook JSON to Mathematica .nb format.

This converter is intentionally minimal and strict:
- It accepts only cell kinds 1 (markdown) and 2 (code)
- It emits a compact text Notebook[...] structure
- It uses BoxData string form for code cells to preserve round-trip fidelity
"""

import argparse
import json
import sys
from pathlib import Path


class ConversionError(Exception):
    """Raised when input data is invalid for conversion."""


def escape_wl_string(value: str) -> str:
    """Escape text for safe embedding in Wolfram notebook source strings."""
    return (
        value.replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("\n", "\\n")
        .replace("\t", "\\t")
        .replace("\r", "\\r")
    )


def markdown_to_cell(value: str) -> str:
    """Convert markdown cell text to a notebook Cell[...] expression."""
    lines = value.splitlines()
    if len(lines) == 1:
        line = lines[0]
        heading_map = (
            ("#### ", "Subsubsection"),
            ("### ", "Subsection"),
            ("## ", "Section"),
            ("# ", "Title"),
        )
        for marker, cell_type in heading_map:
            if line.startswith(marker):
                heading_text = line[len(marker) :]
                return f'Cell["{escape_wl_string(heading_text)}", "{cell_type}"]'

    return f'Cell["{escape_wl_string(value)}", "Text"]'


def code_to_cell(value: str) -> str:
    """Convert code cell text to an Input cell expression."""
    return f'Cell[BoxData["{escape_wl_string(value)}"], "Input"]'


def validate_cell(cell: object, index: int) -> tuple[int, str]:
    """Validate a single cell object and return (kind, value)."""
    if not isinstance(cell, dict):
        raise ConversionError(
            f"Cell {index} is not an object (found {type(cell).__name__})."
        )

    if "kind" not in cell:
        raise ConversionError(f"Cell {index} is missing required key 'kind'.")
    if "value" not in cell:
        raise ConversionError(f"Cell {index} is missing required key 'value'.")

    kind = cell["kind"]
    value = cell["value"]

    if isinstance(kind, bool) or not isinstance(kind, int):
        raise ConversionError(
            f"Cell {index} has non-integer kind: {kind!r} ({type(kind).__name__})."
        )
    if kind not in (1, 2):
        raise ConversionError(f"Cell {index} has unsupported kind {kind}.")
    if not isinstance(value, str):
        raise ConversionError(
            f"Cell {index} has non-string value ({type(value).__name__})."
        )

    return kind, value


def load_wlnb(path: Path) -> list[tuple[int, str]]:
    """Load and validate notebook cells from a .wlnb JSON file."""
    try:
        with path.open("r", encoding="utf-8") as handle:
            data = json.load(handle)
    except json.JSONDecodeError as exc:
        raise ConversionError(f"Invalid JSON in {path}: {exc}") from exc
    except OSError as exc:
        raise ConversionError(f"Unable to read {path}: {exc}") from exc

    if not isinstance(data, dict):
        raise ConversionError(
            f"Top-level JSON must be an object (found {type(data).__name__})."
        )

    cells_raw = data.get("cells")
    if not isinstance(cells_raw, list):
        raise ConversionError(
            "Input notebook must contain a top-level 'cells' array."
        )

    cells: list[tuple[int, str]] = []
    for i, cell in enumerate(cells_raw, start=1):
        cells.append(validate_cell(cell, i))
    return cells


def build_notebook_source(cells: list[tuple[int, str]]) -> str:
    """Serialize validated cells into a text .nb Notebook[...] expression."""
    rendered_cells = []
    for kind, value in cells:
        if kind == 2:
            rendered_cells.append(code_to_cell(value))
        else:
            rendered_cells.append(markdown_to_cell(value))

    if rendered_cells:
        body = ",\n\n".join(rendered_cells)
        return f"Notebook[{{\n{body}\n}}]\n"
    return "Notebook[{\n}]\n"


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Convert .wlnb notebook JSON to Mathematica .nb format "
            "(strict round-trip oriented)."
        )
    )
    parser.add_argument("input", help="Input .wlnb file")
    parser.add_argument(
        "output",
        nargs="?",
        default=None,
        help="Output .nb file (default: same name with .nb extension)",
    )
    args = parser.parse_args()

    input_path = Path(args.input)
    output_path = Path(args.output) if args.output else input_path.with_suffix(".nb")

    try:
        print(f"Reading {input_path}...")
        cells = load_wlnb(input_path)
        code_count = sum(1 for kind, _ in cells if kind == 2)
        markdown_count = sum(1 for kind, _ in cells if kind == 1)
        print(f"Found {len(cells)} cells ({code_count} code, {markdown_count} markdown)")

        print(f"Writing {output_path}...")
        source = build_notebook_source(cells)
        output_path.write_text(source, encoding="utf-8")
        print(f"Done! Created {output_path} with {len(cells)} cells")
        return 0
    except ConversionError as exc:
        print(f"Error: {exc}", file=sys.stderr)
        return 1
    except OSError as exc:
        print(f"Error: Unable to write {output_path}: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
