#!/usr/bin/python3
from datetime import timedelta
import json, os, re

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
        return 6
    elif 'MOGrover' in input:
        return 5
    elif 'Grover' in input:
        return 4
    elif 'GHZall' in input:
        return 3
    elif 'GHZzero' in input:
        return 3
    elif 'MOBV' in input:
        return 2
    elif 'BV' in input:
        return 1

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
    elif input == 'read_file_time':
        return 8
    elif input == 'total':
        return 9
    elif input == 'result':
        return 10
    # else:
    #     print(input)

def compare_function3(input):
    if 'lsta' in input: return 1

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
        if 'H2' in file or 'HXH' in file or 'MCToffoli' in file:
            continue
        the_string_to_be_added = ''
        if file.split('/')[1] not in contents:
            the_string_to_be_added += ' & ' + str(int(file.split('/')[2]))
        else:
            the_string_to_be_added += ' & ' + str(int(file.split('/')[2]))
        for tool, data in datas.items():
            if 'before_state' in data:
                del data['before_state']
            if 'before_trans' in data:
                del data['before_trans']
            if 'after_state' in data:
                del data['after_state']
            if 'after_trans' in data:
                del data['after_trans']
            assert data['total'].count('/') == data['result'].count('/')
            if '/' in data['total']:
                data['result2'] = format_duration(parse_duration(str(data['total'].split('/')[0])) + parse_duration(data['result'].split('/')[0])) + '/' + format_duration(parse_duration(str(data['total'].split('/')[1])) + parse_duration(data['result'].split('/')[1]))
            else:
                data['result2'] = format_duration(parse_duration(data['read_file_time']) + parse_duration(str(data['total'])) + parse_duration(data['result']))
            data['result2'] = r'\textbf{' + data['result2'] + r'}'
            the_string_to_be_added += (' & ' + ' & '.join(map(str, list(data.values())))).replace('ERROR', r'\error')
        the_string_to_be_added = the_string_to_be_added.replace('TIMEOUT', r'\TO')
        if file.split('/')[1] not in contents:
            contents[file.split('/')[1]] = the_string_to_be_added + '\\\\\n'
        else:
            contents[file.split('/')[1]] += the_string_to_be_added + '\\\\\n'

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
\newcommand{\tool}[0]{\textsc{LSTAQ}\xspace}
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
\newcommand{\oegroverbench}[0]{\small\textsc{Grover-Iter}\xspace}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}%\pagenumbering{gobble}

%\scalebox{0.01}
{%\hspace{-100pt}
\hoffset=-1in
\voffset=-1in
\setbox0\hbox{
\begin{tabular}{crrrrrrr}\hline
\toprule
  & \multicolumn{1}{c}{$n$} & \multicolumn{1}{c}{\textbf{\#q}} & \multicolumn{1}{c}{\textbf{\#G}} & \multicolumn{1}{c}{read} & \multicolumn{1}{c}{$\post{C}$} & \multicolumn{1}{c}{$\subseteq$}  & \multicolumn{1}{c}{total} \\
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
sysargv1 = 'correct/lsta.json'
name = sysargv1.split('/')[0] # [:-len('.json')].replace('/', '-') #split('/')[1] + '-' + sysargv1.split('/')[2].split('.')[0]
# sys.argv.pop(0)
if not os.path.exists('tables'):
   os.makedirs('tables')
json_to_latex_table(['./correct/lsta.json'], f'./tables/{name}.tex')
os.chdir('./tables')
os.system(f'pdflatex {name}.tex && vips copy {name}.pdf[dpi=600] {name}.jpg')

# https://tex.stackexchange.com/questions/299005/automatic-page-size-to-fit-arbitrary-content
