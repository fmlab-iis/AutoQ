#!/usr/bin/env python3
import sys
import re
import os
from collections import defaultdict
from dataclasses import dataclass
from typing import List, Dict, Set, Tuple, Optional

# --- Lexer ---

@dataclass
class Token:
    type: str
    value: str
    line: int
    column: int

class Lexer:
    TOKENS = [
        ('CONSTANTS', r'Constants'),
        ('ROOT_STATES', r'Root States'),
        ('TRANSITIONS', r'Transitions'),
        ('ASSIGN', r':='),
        ('ARROW', r'->'),
        ('LBRACKET', r'\['),
        ('RBRACKET', r'\]'),
        ('LPAREN', r'\('),
        ('RPAREN', r'\)'),
        ('COMMA', r','),
        ('NUMBER', r'\d+'),
        ('ID', r'[a-zA-Z_][a-zA-Z0-9_]*'),
        # Complex numbers or strings in constants
        ('EXPR', r'[^:=,\n\]\)\s]+'), 
        ('NEWLINE', r'\n'),
        ('SKIP', r'[ \t]+'),
        ('COMMENT', r'//.*'),
        ('MISMATCH', r'.'),
    ]

    def __init__(self, text):
        self.text = text
        self.tokens = []
        self.tokenize()

    def tokenize(self):
        regex = '|'.join(f'(?P<{name}>{pattern})' for name, pattern in self.TOKENS)
        line_num = 1
        line_start = 0
        for mo in re.finditer(regex, self.text):
            kind = mo.lastgroup
            value = mo.group()
            column = mo.start() - line_start
            if kind == 'NEWLINE':
                line_start = mo.end()
                line_num += 1
            elif kind == 'SKIP' or kind == 'COMMENT':
                pass
            elif kind == 'MISMATCH':
                raise RuntimeError(f'{value!r} unexpected on line {line_num}')
            else:
                self.tokens.append(Token(kind, value, line_num, column))
        self.tokens.append(Token('EOF', '', line_num, 0))

# --- Parser ---

class LSTAParser:
    def __init__(self, tokens: List[Token]):
        self.tokens = tokens
        self.pos = 0
        self.constants = {}
        self.roots = []
        self.transitions = []
        self.td_map = defaultdict(list)

    def peek(self) -> Token:
        return self.tokens[self.pos]

    def peek_next(self) -> Token:
        if self.pos + 1 < len(self.tokens):
            return self.tokens[self.pos + 1]
        return Token('EOF', '', 0, 0)

    def consume(self, expected_type=None) -> Token:
        token = self.peek()
        if expected_type and token.type != expected_type:
            raise RuntimeError(f"Expected {expected_type}, got {token.type} ('{token.value}') at line {token.line}, col {token.column}")
        self.pos += 1
        return token

    def parse(self):
        while self.peek().type != 'EOF':
            t = self.peek()
            if t.type == 'CONSTANTS':
                self.parse_constants()
            elif t.type == 'ROOT_STATES':
                self.parse_roots()
            elif t.type == 'TRANSITIONS':
                self.parse_transitions()
            else:
                self.consume() # Skip unknown top-level tokens

    def parse_constants(self):
        self.consume('CONSTANTS')
        while self.peek().type in ('ID', 'NUMBER', 'EXPR'):
            name_token = self.consume()
            self.consume('ASSIGN')
            
            # Expressions can be complex 
            expr_parts = []
            while True:
                t = self.peek()
                if t.type in ('CONSTANTS', 'ROOT_STATES', 'TRANSITIONS', 'EOF'):
                    break
                # If we see an ID followed by ASSIGN, it's the next constant
                if t.type in ('ID', 'NUMBER') and self.peek_next().type == 'ASSIGN':
                    break
                expr_parts.append(self.consume().value)
            
            self.constants[name_token.value] = " ".join(expr_parts)

    def parse_roots(self):
        self.consume('ROOT_STATES')
        while self.peek().type == 'NUMBER':
            self.roots.append(int(self.consume().value))

    def parse_transitions(self):
        self.consume('TRANSITIONS')
        while self.peek().type == 'LBRACKET':
            self.consume('LBRACKET')
            sym = self.consume().value
            self.consume('COMMA')
            tag = self.consume().value
            self.consume('RBRACKET')
            
            children = []
            if self.peek().type == 'LPAREN':
                self.consume('LPAREN')
                while self.peek().type == 'NUMBER':
                    children.append(int(self.consume().value))
                    if self.peek().type == 'COMMA':
                        self.consume('COMMA')
                self.consume('RPAREN')
            
            self.consume('ARROW')
            parent = int(self.consume('NUMBER').value)
            
            self.td_map[parent].append((sym, tag, children))

# --- Visualizer ---

class LSTAVisualizer:
    def __init__(self, filepath):
        self.filepath = filepath
        with open(filepath, 'r') as f:
            lexer = Lexer(f.read())
        self.parser = LSTAParser(lexer.tokens)
        self.parser.parse()

    def print_text(self, state, indent="", prefix="Root"):
        transitions = self.parser.td_map.get(state, [])
        if not transitions:
            print(f"{indent}{prefix} q{state} (Undefined)")
            return

        for sym, tag, children in transitions:
            display_sym = sym
            if sym in self.parser.constants:
                display_sym = self.parser.constants[sym]
            
            label = f"[{display_sym}, {tag}]"
            print(f"{indent}{prefix} {label} -> q{state}")
            
            for i, child in enumerate(children):
                self.print_text(child, indent + "    ", f"{i}:")

    def visualize(self, output_png=None):
        print(f"Visualizing LSTA (Professional Parser): {self.filepath}")
        print("="*40)
        
        dot_lines = [
            "digraph LSTA {",
            '    node [shape=box, style="filled,rounded", fontname="Arial", fillcolor="#f0f0f0"];',
            '    edge [fontname="Arial"];',
            '    rankdir=TB;',
            '    splines=polyline;'
        ]
        
        node_counter = 0
        layers_map = defaultdict(list)

        def get_node_id():
            nonlocal node_counter
            node_counter += 1
            return f"n{node_counter}"

        def build_dot(state, parent_dot_id=None, edge_label="", depth=0):
            transitions = self.parser.td_map.get(state, [])
            if not transitions:
                dot_id = get_node_id()
                label = f'<<TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">' \
                        f'<TR><TD BGCOLOR="#ffcccc"><B>q{state}</B></TD></TR>' \
                        f'<TR><TD><I>Undefined</I></TD></TR>' \
                        f'</TABLE>>'
                dot_lines.append(f'    {dot_id} [label={label}];')
                if parent_dot_id:
                    dot_lines.append(f'    {parent_dot_id} -> {dot_id} [label="{edge_label}"];')
                layers_map[999].append(dot_id)
                return

            for sym, tag, children in transitions:
                dot_id = get_node_id()
                
                is_layer = sym.isdigit()
                display_sym = sym
                if sym in self.parser.constants:
                    display_sym = self.parser.constants[sym]
                
                header_color = "#2C3E50" if is_layer else "#7D6608"
                text_color = "#FFFFFF"
                body_color = "#EBF5FB" if is_layer else "#FEF9E7"
                
                content = f"L{sym}" if is_layer else display_sym
                
                label = f'<<TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">' \
                        f'<TR><TD BGCOLOR="{header_color}"><FONT COLOR="{text_color}"><B>q{state}</B></FONT></TD></TR>' \
                        f'<TR><TD BGCOLOR="{body_color}">{content}<BR/><FONT POINT-SIZE="10">Tag: {tag}</FONT></TD></TR>' \
                        f'</TABLE>>'
                
                dot_lines.append(f'    {dot_id} [label={label}, shape=none, fillcolor=none];')
                
                if parent_dot_id:
                    dot_lines.append(f'    {parent_dot_id} -> {dot_id} [label="{edge_label}"];')
                
                layer_key = int(sym) if is_layer else (depth + 10)
                layers_map[layer_key].append(dot_id)

                for j, child in enumerate(children):
                    build_dot(child, dot_id, str(j), depth + 1)

        for root in self.parser.roots:
            print(f"\nTree for Root q{root}:")
            self.print_text(root)
            build_dot(root)
            
        for layer, nodes in layers_map.items():
            if nodes:
                dot_lines.append(f'    {{ rank=same; {" ".join(nodes)} }}')

        dot_lines.append("}")
        dot_content = "\n".join(dot_lines)
        
        if output_png:
            import subprocess
            dot_file = output_png.replace(".png", ".dot")
            with open(dot_file, "w") as f:
                f.write(dot_content)
            try:
                subprocess.run(["dot", "-Tpng", dot_file, "-o", output_png], check=True)
                print(f"\n[OK] Professional visualization saved to: {output_png}")
            except Exception as e:
                print(f"\n[Error] Failed to run graphviz: {e}")
        
        print("="*40)

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python3 lsta_visualizer.py <file.lsta> [output.png]")
        sys.exit(1)
    
    output_img = sys.argv[2] if len(sys.argv) > 2 else "tree_viz_pro.png"
    try:
        visualizer = LSTAVisualizer(sys.argv[1])
        visualizer.visualize(output_img)
    except Exception as e:
        print(f"Error: {e}")
        sys.exit(1)
