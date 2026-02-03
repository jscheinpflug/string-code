#!/usr/bin/env python3
"""
Convert Mathematica .nb file to .wlnb format for VSCode Wolfram extension.
Properly parses the Box structure to extract Input cells.
"""

import re
import json
import argparse
from pathlib import Path


def tokenize(s):
    """Tokenize Mathematica expression."""
    tokens = []
    i = 0
    while i < len(s):
        # Skip whitespace
        while i < len(s) and s[i] in ' \t\n\r':
            i += 1
        if i >= len(s):
            break

        # String literal
        if s[i] == '"':
            j = i + 1
            while j < len(s):
                if s[j] == '\\' and j + 1 < len(s):
                    j += 2
                elif s[j] == '"':
                    break
                else:
                    j += 1
            tokens.append(('STRING', s[i+1:j]))
            i = j + 1
        # Brackets
        elif s[i] in '[]{}(),':
            tokens.append((s[i], s[i]))
            i += 1
        # Symbol/Number
        elif s[i].isalnum() or s[i] in '_`$':
            j = i
            while j < len(s) and (s[j].isalnum() or s[j] in '_`$*^'):
                j += 1
            tokens.append(('SYMBOL', s[i:j]))
            i = j
        # Arrow ->
        elif s[i:i+2] == '->':
            tokens.append(('->', '->'))
            i += 2
        # Rule :>
        elif s[i:i+2] == ':>':
            tokens.append((':>', ':>'))
            i += 2
        # Other operators
        elif s[i] in '+-/*^=<>!@#&|;:.':
            tokens.append(('OP', s[i]))
            i += 1
        else:
            i += 1

    return tokens


class Parser:
    """Parse Mathematica expressions from tokens."""

    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0

    def peek(self):
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return None

    def consume(self):
        tok = self.peek()
        self.pos += 1
        return tok

    def parse_expr(self):
        """Parse a general expression."""
        tok = self.peek()
        if tok is None:
            return None

        if tok[0] == 'SYMBOL':
            return self.parse_function_or_symbol()
        elif tok[0] == 'STRING':
            self.consume()
            return ('string', tok[1])
        elif tok[0] == '{':
            return self.parse_list()
        elif tok[0] == '(':
            self.consume()
            inner = self.parse_expr()
            if self.peek() and self.peek()[0] == ')':
                self.consume()
            return inner
        else:
            self.consume()
            return None

    def parse_function_or_symbol(self):
        """Parse Function[...] or just Symbol."""
        tok = self.consume()
        name = tok[1]

        if self.peek() and self.peek()[0] == '[':
            # Function call
            self.consume()  # [
            args = []
            while self.peek() and self.peek()[0] != ']':
                arg = self.parse_expr()
                if arg:
                    args.append(arg)
                if self.peek() and self.peek()[0] == ',':
                    self.consume()
            if self.peek() and self.peek()[0] == ']':
                self.consume()  # ]
            return ('func', name, args)
        else:
            return ('symbol', name)

    def parse_list(self):
        """Parse {a, b, c}."""
        self.consume()  # {
        items = []
        while self.peek() and self.peek()[0] != '}':
            item = self.parse_expr()
            if item:
                items.append(item)
            if self.peek() and self.peek()[0] == ',':
                self.consume()
        if self.peek() and self.peek()[0] == '}':
            self.consume()  # }
        return ('list', items)


def box_to_code(expr):
    """Convert a parsed Box expression to Wolfram code."""
    if expr is None:
        return ""

    if isinstance(expr, str):
        return expr

    if expr[0] == 'string':
        val = expr[1]
        # Unescape
        val = val.replace('\\n', '\n')
        val = val.replace('\\t', '\t')
        val = val.replace('\\"', '"')
        val = val.replace('\\\\', '\\')
        return val

    if expr[0] == 'symbol':
        return expr[1]

    if expr[0] == 'list':
        parts = [box_to_code(item) for item in expr[1]]
        return ''.join(parts)

    if expr[0] == 'func':
        name = expr[1]
        args = expr[2]

        if name == 'RowBox':
            # RowBox[{...}] - join contents
            if args and args[0][0] == 'list':
                parts = [box_to_code(item) for item in args[0][1]]
                return ''.join(parts)
            return ''.join(box_to_code(a) for a in args)

        elif name == 'Cell':
            # Cell[BoxData[...], "Type", ...]
            if len(args) >= 2:
                # Check cell type
                cell_type = None
                for arg in args[1:]:
                    if arg[0] == 'string':
                        cell_type = arg[1]
                        break

                if cell_type == 'Input':
                    # Extract BoxData content
                    if args[0][0] == 'func' and args[0][1] == 'BoxData':
                        return box_to_code(args[0])
            return ""

        elif name == 'BoxData':
            # BoxData[content]
            if args:
                return box_to_code(args[0])
            return ""

        elif name == 'SuperscriptBox':
            # SuperscriptBox[base, exp]
            if len(args) >= 2:
                base = box_to_code(args[0])
                exp = box_to_code(args[1])
                return f"{base}^{exp}"
            return ""

        elif name == 'SubscriptBox':
            # SubscriptBox[base, sub]
            if len(args) >= 2:
                base = box_to_code(args[0])
                sub = box_to_code(args[1])
                return f"Subscript[{base}, {sub}]"
            return ""

        elif name == 'FractionBox':
            # FractionBox[num, denom]
            if len(args) >= 2:
                num = box_to_code(args[0])
                denom = box_to_code(args[1])
                return f"({num})/({denom})"
            return ""

        elif name == 'SqrtBox':
            if args:
                return f"Sqrt[{box_to_code(args[0])}]"
            return ""

        elif name == 'RadicalBox':
            if len(args) >= 2:
                return f"({box_to_code(args[0])})^(1/{box_to_code(args[1])})"
            return ""

        elif name in ('StyleBox', 'FormBox', 'TagBox', 'InterpretationBox',
                     'TooltipBox', 'TemplateBox'):
            # These wrap content, extract first arg
            if args:
                return box_to_code(args[0])
            return ""

        elif name == 'GridBox':
            # Grid of expressions
            if args and args[0][0] == 'list':
                rows = []
                for row in args[0][1]:
                    if row[0] == 'list':
                        cols = [box_to_code(c) for c in row[1]]
                        rows.append(', '.join(cols))
                return '{{' + '}, {'.join(rows) + '}}'
            return ""

        else:
            # Unknown function, try to reconstruct
            if args:
                arg_strs = [box_to_code(a) for a in args]
                return f"{name}[{', '.join(arg_strs)}]"
            return name

    return ""


def find_cell_end(content, start):
    """Find the end of a Cell[...] expression, handling nested brackets.

    start should be the position right after 'Cell[', so we start with depth=1
    to account for the opening bracket of Cell[.
    """
    bracket_depth = 1  # We're already inside Cell[
    i = start
    in_string = False
    escape = False

    while i < len(content):
        if escape:
            escape = False
            i += 1
            continue

        c = content[i]

        if c == '\\':
            escape = True
        elif c == '"' and not escape:
            in_string = not in_string
        elif not in_string:
            if c == '[':
                bracket_depth += 1
            elif c == ']':
                bracket_depth -= 1
                if bracket_depth == 0:
                    return i
        i += 1

    return len(content) - 1


def extract_all_cells(content):
    """Extract all cells from notebook content including sections and comments."""
    cells = []

    # Process all cells sequentially by finding Cell[ patterns
    i = 0
    while i < len(content):
        # Find next Cell[
        cell_idx = content.find('Cell[', i)
        if cell_idx == -1:
            break

        # Check what follows Cell[ - skip CellGroupData and other non-content cells
        after_cell = content[cell_idx + 5:cell_idx + 50].lstrip()

        # Only process content cells (BoxData, direct string, or TextData)
        if not (after_cell.startswith('BoxData[') or
                after_cell.startswith('"') or
                after_cell.startswith('TextData[')):
            i = cell_idx + 5
            continue

        # Find the end of this Cell
        cell_end = find_cell_end(content, cell_idx + 5)
        cell_content = content[cell_idx:cell_end + 1]

        # Determine cell type by looking for the type string
        cell_type = None
        # Look for patterns like , "Input", or , "Title", etc.
        type_match = re.search(r',\s*"(Input|Title|Section|Subsection|Subsubsection|Text)"', cell_content)
        if type_match:
            cell_type = type_match.group(1)

        if cell_type:
            code = None

            if 'BoxData[' in cell_content[:100]:
                # Parse BoxData content
                try:
                    tokens = tokenize(cell_content)
                    parser = Parser(tokens)
                    expr = parser.parse_expr()
                    code = box_to_code(expr)
                    code = clean_wolfram_code(code.strip())
                except Exception as e:
                    pass
            elif re.match(r'Cell\s*\[\s*"', cell_content):
                # Simple Cell["text", "Type"] format
                match = re.search(r'Cell\s*\[\s*"([^"]*)"', cell_content)
                if match:
                    code = match.group(1)
            elif 'TextData[' in cell_content[:100]:
                # Cell[TextData[...], "Type"] format - extract text from StyleBox or direct strings
                # Find all quoted strings that aren't cell metadata
                text_end = cell_content.find(', "' + cell_type)
                if text_end == -1:
                    text_end = len(cell_content)
                text_part = cell_content[:text_end]
                strings = []
                in_str = False
                current = []
                esc = False
                for c in text_part:
                    if esc:
                        current.append(c)
                        esc = False
                    elif c == '\\':
                        esc = True
                    elif c == '"':
                        if in_str:
                            s = ''.join(current)
                            # Filter out metadata
                            if not (s in ['Section', 'Subsection', 'Title', 'Text', 'StyleBox'] or
                                   re.match(r'^\d+\.\d+\*\^9', s) or
                                   re.match(r'^[a-f0-9-]{36}$', s)):
                                strings.append(s)
                            current = []
                        in_str = not in_str
                    elif in_str:
                        current.append(c)
                code = ''.join(strings)

            if code and code.strip():
                code = code.strip()
                if cell_type in ['Title', 'Section', 'Subsection', 'Subsubsection', 'Text']:
                    # Convert to markdown
                    if cell_type == 'Title':
                        cells.append(('markdown', f'# {code}'))
                    elif cell_type == 'Section':
                        cells.append(('markdown', f'## {code}'))
                    elif cell_type == 'Subsection':
                        cells.append(('markdown', f'### {code}'))
                    elif cell_type == 'Subsubsection':
                        cells.append(('markdown', f'#### {code}'))
                    else:  # Text
                        cells.append(('markdown', code))
                elif cell_type == 'Input':
                    # Check if it's a comment-only cell
                    if code.startswith('(*') and code.endswith('*)'):
                        # Convert comment to markdown
                        comment_text = code[2:-2].strip()
                        cells.append(('markdown', comment_text))
                    else:
                        cells.append(('code', code))

        i = cell_end + 1

    return cells


def clean_wolfram_code(code):
    """Clean up Wolfram Language code from .nb format artifacts."""
    # Remove \< and \> string delimiters (Mathematica uses these in .nb files)
    code = code.replace('\\<', '')
    code = code.replace('\\>', '')

    # Replace \[IndentingNewLine] with actual newlines
    code = code.replace('\\[IndentingNewLine]', '\n')

    # Keep Greek letters and other special characters as-is (they work in Wolfram)
    # \[Mu], \[Alpha], etc. are valid Wolfram syntax

    return code


def extract_cells_regex(content):
    """Fallback regex-based extraction."""
    cells = []

    # Split by Input cell markers
    parts = re.split(r'Cell\[BoxData\[', content)

    for part in parts[1:]:
        # Check if it's an Input cell
        if ', "Input",' not in part and ',"Input",' not in part:
            continue

        # Find end of BoxData
        bracket_count = 1
        j = 0
        while j < len(part) and bracket_count > 0:
            if part[j] == '[':
                bracket_count += 1
            elif part[j] == ']':
                bracket_count -= 1
            j += 1

        boxdata = part[:j-1]

        # Extract strings from RowBox structure
        strings = []
        in_string = False
        current = []
        escape = False

        for c in boxdata:
            if escape:
                if c == 'n':
                    current.append('\n')
                elif c == 't':
                    current.append('\t')
                elif c == '"':
                    current.append('"')
                elif c == '\\':
                    current.append('\\')
                elif c == '[':
                    current.append('[')
                elif c == ']':
                    current.append(']')
                else:
                    current.append(c)
                escape = False
            elif c == '\\':
                escape = True
            elif c == '"':
                if in_string:
                    s = ''.join(current)
                    # Filter metadata
                    if not (re.match(r'^\d+\.\d+\*\^9', s) or
                           re.match(r'^[a-f0-9-]{36}$', s) or
                           s.startswith('In[') or s.startswith('Out[') or
                           s.startswith('CellChangeTimes') or
                           s.startswith('ExpressionUUID')):
                        strings.append(s)
                    current = []
                in_string = not in_string
            elif in_string:
                current.append(c)

        code = ''.join(strings)
        code = clean_wolfram_code(code)
        if code.strip():
            cells.append(code.strip())

    return cells


def create_wlnb(cells):
    """Create .wlnb format (VSCode Notebook format)."""
    notebook = {
        "cells": []
    }

    for cell_data in cells:
        if isinstance(cell_data, tuple):
            cell_type, content = cell_data
            if content.strip():
                if cell_type == 'markdown':
                    cell = {
                        "kind": 1,  # 1 = markdown
                        "value": content,
                        "languageId": "markdown"
                    }
                else:  # code
                    cell = {
                        "kind": 2,  # 2 = code
                        "value": content,
                        "languageId": "wolfram"
                    }
                notebook["cells"].append(cell)
        else:
            # Legacy: plain string = code cell
            if cell_data.strip():
                cell = {
                    "kind": 2,
                    "value": cell_data,
                    "languageId": "wolfram"
                }
                notebook["cells"].append(cell)

    return notebook


def main():
    parser = argparse.ArgumentParser(
        description="Convert Mathematica .nb file to .wlnb format for VSCode Wolfram extension."
    )
    parser.add_argument("input", help="Input .nb file")
    parser.add_argument(
        "output",
        nargs="?",
        default=None,
        help="Output .wlnb file (default: same name with .wlnb extension)"
    )
    args = parser.parse_args()

    input_file = args.input
    if args.output:
        output_file = args.output
    else:
        output_file = str(Path(input_file).with_suffix(".wlnb"))

    print(f"Reading {input_file}...")
    with open(input_file, 'r', encoding='utf-8', errors='replace') as f:
        content = f.read()

    print("Extracting all cells (including sections and comments)...")
    cells = extract_all_cells(content)

    # Count cell types
    markdown_count = sum(1 for c in cells if isinstance(c, tuple) and c[0] == 'markdown')
    code_count = sum(1 for c in cells if isinstance(c, tuple) and c[0] == 'code')

    print(f"Found {len(cells)} cells ({code_count} code, {markdown_count} markdown)")

    if cells:
        print("\n--- Preview of first 5 cells ---")
        for i, c in enumerate(cells[:5]):
            if isinstance(c, tuple):
                cell_type, content = c
                preview = content[:100] + "..." if len(content) > 100 else content
                print(f"\nCell {i+1} [{cell_type}]:\n{preview}")

    print(f"\nWriting {output_file}...")
    notebook = create_wlnb(cells)

    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(notebook, f, indent=2, ensure_ascii=False)

    print(f"Done! Created {output_file} with {len(notebook['cells'])} cells")


if __name__ == "__main__":
    main()
