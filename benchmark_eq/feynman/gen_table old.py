#!/usr/bin/python3
import json, os, sys

def merge_json_files(file_list):
    merged_data = {}
    for file in file_list:
        with open(file, 'r') as f:
            data = json.load(f)
            for key, value in data.items():
                print(file, key, value)
                key = '.'.join(key.split('.')[:-1])
                if key not in merged_data:
                    merged_data[key] = {'q': value['q'], 'G': value['G'], 'G2': value['G2'], 'total': [], 'result': []}
                merged_data[key]['total'].append(value['total'])
                merged_data[key]['result'].append(value['result'])
    print(merged_data)
    return merged_data

def json_to_latex_table(file_list, latex_filename):
    merged_data = merge_json_files(file_list)

    # Create the LaTeX table
    latex_code = """
\\documentclass{article}
\\usepackage{booktabs}
\\usepackage{geometry}
\\geometry{a4paper, margin=1in, paperwidth=40cm, paperheight=40cm}
\\begin{document}

\\begin{table}[h!]
\\centering
\\begin{tabular}{|l|c|c|c|""" + "c|c|" * len(file_list) + """}
\\hline
Filename & q & G & G2 & """ + " & ".join(f"t ({f.split('/')[1].split('.json')[0]}) & s ({f.split('/')[1].split('.json')[0]})" for f in file_list) + """ \\\\ \\hline
"""

    merged_data = dict(sorted(merged_data.items(), key=lambda item: (item[0], int(item[1]['q']))))
    for filename, values in merged_data.items():
        row = [filename, values['q'], values['G'], values['G2']]
        for i in range(len(file_list)):
            row.append(values['total'][i] if i < len(values['total']) else '-')
            row.append(values['result'][i] if i < len(values['result']) else '-')
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
