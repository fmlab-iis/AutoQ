#!/usr/bin/python3
# import os, re, subprocess
# from ctypes import c_wchar_p
# from multiprocessing import Manager, Process, Semaphore, Lock

# content = []
# for row in string_pool_large:
#     content.append(list(map(lambda x: x.value, row)))
# content.sort(key = lambda x: x[0])

# # print(content)

# for i in range(len(content)):
#     content[i][0] = content[i][0].split('/')[-1].lstrip('0')
#     content[i].insert(0, '')
#     content[i] = ' & '.join(content[i])

# contents = dict()
# contents['bvsingbench'] = ''.join(content[i] + '\\\\\n' for i in range(0, 5))
# contents['ghzmultbench'] = ''.join(content[i] + '\\\\\n' for i in range(5, 10))
# contents['ghzsingbench'] = ''.join(content[i] + '\\\\\n' for i in range(10, 15))
# contents['groversingbench'] = ''.join(content[i] + '\\\\\n' for i in range(15, 20))
# contents['hhbench'] = ''.join(content[i] + '\\\\\n' for i in range(20, 25))
# contents['hxhbench'] = ''.join(content[i] + '\\\\\n' for i in range(25, 30))
# contents['mctoffolibench'] = ''.join(content[i] + '\\\\\n' for i in range(30, 35))
# contents['bvmultbench'] = ''.join(content[i] + '\\\\\n' for i in range(35, 40))
# contents['grovermultbench'] = ''.join(content[i] + '\\\\\n' for i in range(40, 45))

# f = open(name, 'w')
# print(r'''\documentclass{article}

# \usepackage{booktabs}
# \usepackage{xspace}
# \usepackage{multicol}
# \usepackage{multirow}
# \usepackage{graphicx}
# \usepackage{colortbl}
# \usepackage{xcolor}

# % tool names
# \newcommand{\autoq}[0]{\textsc{AutoQ}\xspace}
# \newcommand{\sliqsim}[0]{\textsc{SliQSim}\xspace}
# \newcommand{\feynman}[0]{\textsc{Feynman}\xspace}
# \newcommand{\feynopt}[0]{\textsc{Feynopt}\xspace}
# \newcommand{\qcec}[0]{\textsc{Qcec}\xspace}
# \newcommand{\qbricks}[0]{\textsc{Qbricks}\xspace}
# \newcommand{\qiskit}[0]{\textsc{Qiskit}\xspace}
# \newcommand{\vata}[0]{\textsc{Vata}\xspace}
# \newcommand{\cta}[0]{\textsc{CTA}\xspace}
# \newcommand{\ta}[0]{\textsc{TA}\xspace}
# \newcommand{\correct}[0]{T\xspace}
# \newcommand{\wrong}[0]{F\xspace}
# \newcommand{\unknown}[0]{---\xspace}
# \newcommand{\nacell}[0]{\cellcolor{black!20}}
# \newcommand{\timeout}[0]{\nacell timeout}
# \newcommand{\error}[0]{\nacell error}
# %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
# \newcommand{\post}[1]{\mathtt{post}_{#1}}

# % benchmarks
# \newcommand{\bvsingbench}[0]{\small\textsc{BV-Sing}\xspace}
# \newcommand{\bvmultbench}[0]{\small\textsc{BV-All}\xspace}
# \newcommand{\ghzsingbench}[0]{\small\textsc{GHZ-Sing}\xspace}
# \newcommand{\ghzmultbench}[0]{\small\textsc{GHZ-All}\xspace}
# \newcommand{\groversingbench}[0]{\small\textsc{Grover-Sing}\xspace}
# \newcommand{\grovermultbench}[0]{\small\textsc{Grover-All}\xspace}
# \newcommand{\hhbench}[0]{\small\textsc{H2}\xspace}
# \newcommand{\hxhbench}[0]{\small\textsc{HXH}\xspace}
# \newcommand{\mctoffolibench}[0]{\small\textsc{MCToffoli}\xspace}
# \newcommand{\randombench}[0]{\textsc{Random}\xspace}
# \newcommand{\revlibbench}[0]{\textsc{RevLib}\xspace}
# \newcommand{\feynmanbench}[0]{\textsc{FeynmanBench}\xspace}
# %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

# \begin{document}\pagenumbering{gobble}

# %\scalebox{0.6}
# {\hspace{-100pt}
# \begin{tabular}{crrrrrrrrrrrrrrrrrr}\hline
# \toprule
#   &&&& \multicolumn{6}{c}{\cta} & \multicolumn{6}{c}{\autoq} & \multirow{2}{*}{SV-Sim} & \multirow{2}{*}{symQV} & \multirow{2}{*}{CaAL}\\
#   \cmidrule(lr){5-10} \cmidrule(lr){11-16}
#   & \multicolumn{1}{c}{$n$} & \multicolumn{1}{c}{\textbf{\#q}} & \multicolumn{1}{c}{\textbf{\#G}} & \multicolumn{2}{c}{\textbf{before}} & \multicolumn{2}{c}{\textbf{after}} & \multicolumn{1}{c}{$\post{C}$} & \multicolumn{1}{c}{$\subseteq$} & \multicolumn{2}{c}{\textbf{before}} & \multicolumn{2}{c}{\textbf{after}} & \multicolumn{1}{c}{$\post{C}$} & \multicolumn{1}{c}{$\subseteq$}\\
# \midrule
#   \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\bvsingbench}}
# ''' +
#   contents['bvsingbench'] +
# r'''\midrule
#   \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\bvmultbench}}
# ''' +
#   contents['bvmultbench'] +
# r'''\midrule
# \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\ghzsingbench}}
# ''' +
#   contents['ghzsingbench'] +
# r'''\midrule
#   \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\ghzmultbench}}
# ''' +
#   contents['ghzmultbench'] +
# r'''\midrule
#   \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\groversingbench}}
# ''' +
#   contents['groversingbench'] +
# r'''\midrule
#   \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\grovermultbench}}
# ''' +
#   contents['grovermultbench'] +
# r'''\midrule
#   \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\hhbench}}
# ''' +
#   contents['hhbench'] +
# r'''\midrule
#   \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\hxhbench}}
# ''' +
#   contents['hxhbench'] +
# r'''\midrule
#   \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\mctoffolibench}}
# ''' +
#   contents['mctoffolibench'] +
# r'''\bottomrule
# \end{tabular}
# }

# \end{document}'''
# , file=f)

# f.close()

# os.system(f'pdflatex {name}')

import json, os, sys

def compare_function(input):
    if 'MCToffoli' in input:
        return 9
    elif 'MOGrover' in input:
        return 6
    elif 'MOBV' in input:
        return 2
    elif 'Grover' in input:
        return 5
    elif 'BV' in input:
        return 1
    elif 'GHZzero' in input:
        return 3
    elif 'GHZall' in input:
        return 4
    elif 'H2' in input:
        return 7
    elif 'HXH' in input:
        return 8

def compare_function2(input):
    if input == 'q':
        return 1
    elif input == 'G':
        return 2
    elif input == 'before_state':
        return 4
    elif input == 'before_trans':
        return 5
    elif input == 'after_state':
        return 6
    elif input == 'after_trans':
        return 7
    elif input == 'total':
        return 8
    elif input == 'result':
        return 9
    # else:
    #     print(input)

def compare_function3(input):
    if 'lsta' in input: return 1
    if 'autoq' in input: return 2
    if 'sliqsim' in input: return 3
    if 'svsim' in input: return 4
    if 'symqv' in input: return 5
    if 'caal' in input: return 6

def merge_json_files(tool_list):
    headers_in_a_tool = {}
    merged_data = {}
    tool_list.sort(key=lambda val: compare_function3(val))
    for tool in tool_list:
        with open(tool, 'r') as f:
            data = json.load(f)
            for file, value in data.items():
                value = dict(sorted(value.items(), key=lambda item: compare_function2(item[0])))
                if file not in merged_data:
                    merged_data[file] = {}
                merged_data[file][tool] = value
                if tool not in headers_in_a_tool:
                    headers_in_a_tool[tool] = value.keys()
                else:
                    headers_in_a_tool[tool] |= value.keys()
    for file, v in merged_data.items():
        for tool, data in v.items():
            for header in headers_in_a_tool[tool]:
                if header not in data:
                    data[header] = '---'
    return merged_data

def json_to_latex_table(tool_list, latex_filename):
    merged_data = merge_json_files(tool_list)
    merged_data = dict(sorted(merged_data.items(), key=lambda item: (compare_function(item[0]), int(next(iter(item[1].values()))['q']))))

    headers = []
    for tool, data in next(iter(merged_data.values())).items():
        for k, v in data.items():
            if k not in ('q', 'G'):
                headers.append(tool[:-len('.json')].split('/')[-1] + '-' + k)

    # Create the LaTeX table
    latex_code = """
\\documentclass{article}
\\usepackage{booktabs}
\\usepackage{geometry}
\\geometry{a4paper, margin=1in, paperwidth=150cm, paperheight=40cm}
\\begin{document}

\\begin{table}[h!]
\\centering
\\begin{tabular}{|l|c|c|""" + "c|" * len(headers) + """}
\\hline
Filename & q & G & """ + " & ".join(headers) + """ \\\\ \\hline
"""
    # print(merged_data)
    for filename, data in merged_data.items():
        row = [filename, next(iter(data.values()))['q'], next(iter(data.values()))['G']]
        for tool, cols in data.items():
            for k, v in cols.items():
                if k not in ('q', 'G'):
                    row.append(v)
        latex_code += " & ".join(map(str, row)) + " \\\\ \\hline\n"

    latex_code += """
\\end{tabular}
\\""" + f"caption{{{latex_filename[:-len('.tex')]}}}" + """
%label{table:your_label_here}
\\end{table}

\\end{document}
"""

    # Write the LaTeX code to a file
    latex_code = latex_code.replace('_', '\\_').replace('^', '\\^{}')
    with open(latex_filename, 'w') as file:
        file.write(latex_code)

# Example usage
# sys.argv[1] = './feynopt/qcec.json'
name = sys.argv[1].split('/')[0] # [:-len('.json')].replace('/', '-') #split('/')[1] + '-' + sys.argv[1].split('/')[2].split('.')[0]
sys.argv.pop(0)
json_to_latex_table(sys.argv, f'./tables/{name}.tex')
os.chdir('./tables')
os.system(f'pdflatex {name}.tex')
