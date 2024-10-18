#!/usr/bin/python3
from datetime import timedelta
import json, os, re, sys

def parse_duration(duration_str):
    pattern = r'((?P<minutes>\d+)m)?((?P<seconds>\d+(\.\d+)?)s)?'
    match = re.match(pattern, duration_str)
    if not match:
        raise ValueError("Invalid duration format")

    parts = match.groupdict()
    minutes = int(parts['minutes']) if parts['minutes'] else 0
    seconds = float(parts['seconds']) if parts['seconds'] else 0.0

    return timedelta(minutes=minutes, seconds=seconds)

def format_duration(duration):
    total_seconds = duration.total_seconds()
    minutes, seconds = divmod(total_seconds, 60)

    if minutes >= 1:
        formatted_duration = f"{int(minutes)}m{int(round(seconds))}s"
    else:
        formatted_duration = f"{seconds:.1f}s"

    # Remove the trailing zero after decimal point if it's a whole number
    if seconds > 0 and formatted_duration.endswith(".0s"):
        formatted_duration = formatted_duration.replace(".0s", "s")

    return formatted_duration

def compare_function(input):
    if 'OEGrover' in input:
        return 10
    elif 'MCToffoli' in input:
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
                # print(62, value)
                # value = dict(sorted(value.items(), key=lambda item: compare_function2(item[0])))
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
                    merged_data[file][tool][header] = '---'
                    # data[header] = '---'
            merged_data[file][tool] = dict(sorted(merged_data[file][tool].items(), key=lambda item: compare_function2(item[0])))
    return merged_data

def json_to_latex_table(tool_list, latex_filename):
    merged_data = merge_json_files(tool_list)
    merged_data = dict(sorted(merged_data.items(), key=lambda item: (compare_function(item[0]), int(next(iter(item[1].values()))['q']))))

    # headers = []
    # for tool, data in next(iter(merged_data.values())).items():
    #     for k, v in data.items():
    #         if k not in ('q', 'G'):
    #             headers.append(tool[:-len('.json')].split('/')[-1] + '-' + k)

    contents = dict()
    for file, datas in merged_data.items():
        the_string_to_be_added = ''
        if file.split('/')[1] not in contents:
            the_string_to_be_added += ' & ' + str(int(file.split('/')[2]))
        else:
            the_string_to_be_added += ' & ' + str(int(file.split('/')[2]))
        tool_before = 0
        for tool, data in datas.items():
            tmp = compare_function3(tool)
            if tmp > tool_before + 1:
                the_string_to_be_added += (tmp - tool_before - 1) * ' & -'
            tool_before = tmp
            if 'before_state' in data:
                del data['before_state']
            if 'before_trans' in data:
                del data['before_trans'] #= '(' + data['before_trans'] + ')'
            if 'after_state' in data:
                del data['after_state']
            if 'after_trans' in data:
                del data['after_trans'] #= '(' + data['after_trans'] + ')'
            if 'lsta' not in tool:
                del data['q']
                del data['G']
                if data['result'] == '1' or data['result'] == 'O':
                    data['result'] = format_duration(parse_duration(str(data['total'])))
                elif 'autoq' in tool:
                    if data['result'] not in ('TIMEOUT', 'ERROR'):
                        if ('OEGrover' in file and data['result'] != '0') or ('OEGrover' not in file and 'V' not in data['result']):
                            data['result'] = 'WRONG'
                        else:
                            assert data['total'].count('/') == data['result'].count('/')
                            if data['result'] == 'V/V':
                                data['result'] = data['total']
                            elif '/' in data['total']:
                                data['result'] = format_duration(parse_duration(str(data['total'].split('/')[0])) + parse_duration(data['result'].split('/')[0])) + '/' + format_duration(parse_duration(str(data['total'].split('/')[1])) + parse_duration(data['result'].split('/')[1]))
                            else:
                                data['result'] = format_duration(parse_duration(str(data['total'])) + parse_duration(data['result']))
                del data['total']
            else:
                assert ('/' not in data['result'] and data['result'].endswith(' X')) or ('/' in data['result'] and data['result'].count(' X') == 2)
                data['result'] = data['result'].replace(' X', '')
                assert data['total'].count('/') == data['result'].count('/')
                if '/' in data['total']:
                    data['result2'] = format_duration(parse_duration(str(data['total'].split('/')[0])) + parse_duration(data['result'].split('/')[0])) + '/' + format_duration(parse_duration(str(data['total'].split('/')[1])) + parse_duration(data['result'].split('/')[1]))
                else:
                    data['result2'] = format_duration(parse_duration(str(data['total'])) + parse_duration(data['result']))
                data['result2'] = r'\textbf{' + data['result2'] + r'}'
            if 'autoq' in tool:
                data = {'result': data['result']}
            print(file, tool, data, list(data.values()))
            # if 'symqv' in tool:
            #     the_string_to_be_added += (' & ' + ' & '.join(map(str, list(data.values())))).replace('ERROR', r'\timeout')
            # else:
            the_string_to_be_added += (' & ' + ' & '.join(map(str, list(data.values())))).replace('ERROR', r'\error')
        the_string_to_be_added = the_string_to_be_added.replace('TIMEOUT', r'\timeout')
        the_string_to_be_added += (9 - the_string_to_be_added.count('&')) * ' & -'
        if file.split('/')[1] not in contents:
            contents[file.split('/')[1]] = the_string_to_be_added + '\\\\\n'
        else:
            contents[file.split('/')[1]] += the_string_to_be_added + '\\\\\n'
        # print(contents[file.split('/')[1]])

    # Create the LaTeX table
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
\newcommand{\timeout}[0]{\nacell TO}
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

\begin{document}%\pagenumbering{gobble}

%\scalebox{0.01}
{%\hspace{-100pt}
\hoffset=-1in
\voffset=-1in
\setbox0\hbox{
\begin{tabular}{crrrrrrrrrr}\hline
\toprule
  &&&& \multicolumn{3}{c}{\tool} & \multirow{2}{*}{\autoq} & \multirow{2}{*}{symQV} & \multirow{2}{*}{CaAL}\\
  \cmidrule(lr){5-7}
  & \multicolumn{1}{c}{$n$} & \multicolumn{1}{c}{\textbf{\#q}} & \multicolumn{1}{c}{\textbf{\#G}} & \multicolumn{1}{c}{$\post{C}$} & \multicolumn{1}{c}{$\subseteq$} & \multicolumn{1}{c}{total}\\
\midrule
  \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\bvsingbench}}
''' + contents['BV'] + r'''\midrule
  \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\bvmultbench}}
''' + contents['MOBV_reorder'] + r'''\midrule
\multirow{ 5}{*}{\rotatebox[origin=c]{90}{\ghzsingbench}}
''' + contents['GHZzero'] + r'''\midrule
  \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\ghzmultbench}}
''' + contents['GHZall'] + r'''\midrule
  \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\groversingbench}}
''' + contents['Grover'] + r'''\midrule
  \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\grovermultbench}}
''' + contents['MOGrover'] + r'''\midrule
  \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\hhbench}}
''' + contents['H2'] + r'''\midrule
  \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\hxhbench}}
''' + contents['HXH'] + r'''\midrule
  \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\mctoffolibench}}
''' + contents['MCToffoli'] + r'''\midrule
  \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\oegroverbench}}
''' + contents['OEGrover'] + r'''\bottomrule
\end{tabular}
}

\pdfpageheight=\dimexpr\ht0+\dp0\relax
\pdfpagewidth=\wd0
\shipout\box0
\stop

\end{document}'''

    # Write the LaTeX code to a file
    latex_code = latex_code.replace('_', '\\_').replace('^', '\\^{}')
    with open(latex_filename, 'w') as file:
        file.write(latex_code)

# Example usage
# sys.argv[1] = './feynopt/qcec.json'
name = sys.argv[1].split('/')[0] # [:-len('.json')].replace('/', '-') #split('/')[1] + '-' + sys.argv[1].split('/')[2].split('.')[0]
sys.argv.pop(0)
if not os.path.exists('tables'):
   os.makedirs('tables')
json_to_latex_table(sys.argv, f'./tables/{name}.tex')
os.chdir('./tables')
os.system(f'pdflatex {name}.tex && vips copy {name}.pdf[dpi=600] {name}.jpg')

# https://tex.stackexchange.com/questions/299005/automatic-page-size-to-fit-arbitrary-content
