#!/usr/bin/python3
import os, re

largeList = []
with open('./GroverWhile/output.txt', 'r') as f:
    for line in f.readlines():
        # print(re.search(r'(\d+)', line).group(1), re.findall(r'\[(.*?)\]', line))
        smallList = [re.search(r'(\d+)', line).group(1)] + re.findall(r'\[(.*?)\]', line)
        largeList.append(smallList)
with open('./RUS/output.txt', 'r') as f:
    for line in f.readlines():
        largeList.append(re.findall(r'\[(.*?)\]', line))
print(largeList)

latex_code = r'''\documentclass{article}

\usepackage{booktabs}
\usepackage{xspace}
\usepackage{multicol}
\usepackage{multirow}
\usepackage{graphicx}
\usepackage{colortbl}
\usepackage{xcolor}

% tool names
\newcommand{\autoq}[0]{\textsc{AutoQ}\xspace}
\newcommand{\sliqsim}[0]{\textsc{SliQSim}\xspace}
\newcommand{\feynman}[0]{\textsc{Feynman}\xspace}
\newcommand{\feynopt}[0]{\textsc{Feynopt}\xspace}
\newcommand{\qcec}[0]{\textsc{Qcec}\xspace}
\newcommand{\qbricks}[0]{\textsc{Qbricks}\xspace}
\newcommand{\qiskit}[0]{\textsc{Qiskit}\xspace}
\newcommand{\vata}[0]{\textsc{Vata}\xspace}
\newcommand{\tool}[0]{\textsc{LSTAQ}\xspace}
\newcommand{\ta}[0]{\textsc{TA}\xspace}
\newcommand{\correct}[0]{T\xspace}
\newcommand{\wrong}[0]{F\xspace}
\newcommand{\unknown}[0]{---\xspace}
\newcommand{\nacell}[0]{\cellcolor{black!20}}
\newcommand{\TO}[0]{\nacell TO}
\newcommand{\error}[0]{\nacell OOM}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newcommand{\post}[1]{\mathtt{post}_{#1}}

% benchmarks
\newcommand{\bvsingbench}[0]{\small\textsc{BV-Sing}\xspace}
\newcommand{\bvmultbench}[0]{\small\textsc{BV-All}\xspace}
\newcommand{\ghzsingbench}[0]{\small\textsc{GHZ-Sing}\xspace}
\newcommand{\ghzmultbench}[0]{\small\textsc{GHZ-All}\xspace}
\newcommand{\groversingbench}[0]{\small\textsc{Grover-Sing}\xspace}
\newcommand{\grovermultbench}[0]{\small\textsc{Grover-All}\xspace}
\newcommand{\hhbench}[0]{\small\textsc{H2}\xspace}
\newcommand{\hxhbench}[0]{\small\textsc{HXH}\xspace}
\newcommand{\mctoffolibench}[0]{\small\textsc{MCToffoli}\xspace}
\newcommand{\randombench}[0]{\textsc{Random}\xspace}
\newcommand{\revlibbench}[0]{\textsc{RevLib}\xspace}
\newcommand{\feynmanbench}[0]{\textsc{FeynmanBench}\xspace}
\newcommand{\oegroverbench}[0]{\small\textsc{Grover-Iter}\xspace}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}
\hoffset=-1in
\voffset=-1in
\setbox0\hbox{
\begin{tabular}{lrrccrrclrrccrr}\toprule
\multicolumn{7}{c}{\emph{Weakly Measured Grover's Search}~\cite{weakly:chris}} &&
\multicolumn{7}{c}{\emph{Repeat-Until-Success}~\cite{RUS}}\\
\cmidrule{1-7}
\cmidrule{9-15}
\multicolumn{1}{c}{\textbf{program}} &
\multicolumn{1}{c}{\textbf{qubits}} &
\multicolumn{1}{c}{\textbf{gates}} &
~~ &
\multicolumn{1}{c}{\textbf{result}} &
\textbf{time} &
\multicolumn{1}{c}{\textbf{memory}} &
~~ &
\multicolumn{1}{c}{\textbf{program}} &
\multicolumn{1}{c}{\textbf{qubits}} &
\multicolumn{1}{c}{\textbf{gates}} &
~~ &
\multicolumn{1}{c}{\textbf{result}} &
\textbf{time} &
\multicolumn{1}{c}{\textbf{memory}}\\
\cmidrule{1-7}
\cmidrule{9-15}
''' + f'WMGrover ({largeList[0][0]}) & {largeList[0][1]} & {largeList[0][2]} && {largeList[0][3]} & {largeList[0][4]} & {largeList[0][5]} && $(2X+\sqrt2 Y+Z)/\sqrt7$ & {largeList[6][0]} & {largeList[6][1]} && {largeList[6][2]} & {largeList[6][3]} & {largeList[6][4]}' + r'''\\
''' + f'WMGrover ({largeList[1][0]}) & {largeList[1][1]} & {largeList[1][2]} && {largeList[1][3]} & {largeList[1][4]} & {largeList[1][5]} && $(I+i\sqrt2X)/\sqrt3$ & {largeList[7][0]} & {largeList[7][1]} && {largeList[7][2]} & {largeList[7][3]} & {largeList[7][4]}' + r'''\\
''' + f'WMGrover ({largeList[2][0]}) & {largeList[2][1]} & {largeList[2][2]} && {largeList[2][3]} & {largeList[2][4]} & {largeList[2][5]} && $(I+2iZ)/\sqrt{5}$ & {largeList[8][0]} & {largeList[8][1]} && {largeList[8][2]} & {largeList[8][3]} & {largeList[8][4]}' + r'''\\
''' + f'WMGrover ({largeList[3][0]}) & {largeList[3][1]} & {largeList[3][2]} && {largeList[3][3]} & {largeList[3][4]} & {largeList[3][5]} && $(3I+2iZ)/\sqrt{13}$ & {largeList[9][0]} & {largeList[9][1]} && {largeList[9][2]} & {largeList[9][3]} & {largeList[9][4]}' + r'''\\
''' + f'WMGrover ({largeList[4][0]}) & {largeList[4][1]} & {largeList[4][2]} && {largeList[4][3]} & {largeList[4][4]} & {largeList[4][5]} && $(4I+iZ)/\sqrt{17}$ & {largeList[10][0]} & {largeList[10][1]} && {largeList[10][2]} & {largeList[10][3]} & {largeList[10][4]}' + r'''\\
''' + f'WMGrover ({largeList[5][0]}) & {largeList[5][1]} & {largeList[5][2]} && {largeList[5][3]} & {largeList[5][4]} & {largeList[5][5]} && $(5I+2iZ)/\sqrt{29}$ & {largeList[11][0]} & {largeList[11][1]} && {largeList[11][2]} & {largeList[11][3]} & {largeList[11][4]}' + r'''\\
\bottomrule
\end{tabular}}
\pdfpageheight=\dimexpr\ht0+\dp0\relax
\pdfpagewidth=\wd0
\shipout\box0
\stop
\end{document}'''

# Write the LaTeX code to a file
latex_code = latex_code.replace('_', '\\_').replace('^', '\\^{}')
with open('Table1.tex', 'w') as file:
    file.write(latex_code)
os.system(f'pdflatex Table1.tex && vips copy Table1.pdf[dpi=600] Table1.jpg')
