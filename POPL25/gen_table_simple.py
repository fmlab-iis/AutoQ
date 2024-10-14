#!/usr/bin/python3
import json, os, sys

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
\\begin{document}

\\hoffset=-1in
\\voffset=-1in
\\setbox0\\hbox{

\\""" + f"{latex_filename[:-len('.tex')]}" + """

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

%label{table:your_label_here}
}

\\pdfpageheight=\\dimexpr\\ht0+\\dp0\\relax
\\pdfpagewidth=\\wd0
\\shipout\\box0
\\stop
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
os.system(f'pdflatex {name}.tex && vips copy {name}.pdf[dpi=600] {name}.jpg')

# https://tex.stackexchange.com/questions/299005/automatic-page-size-to-fit-arbitrary-content