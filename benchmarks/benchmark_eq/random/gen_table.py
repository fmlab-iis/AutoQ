#!/usr/bin/python3
import json, os, sys

def compare_function(input):
    if input == 'q':
        return 1
    elif input == 'G':
        return 2
    elif input == 'G2':
        return 3
    elif input == 'gate':
        return 4
    elif input == 'removeuseless':
        return 5
    elif input == 'reduce':
        return 6
    elif input == 'include':
        return 7
    elif input == 'total':
        return 8
    elif input == 'result':
        return 9
    elif input == 'aut1.trans':
        return 10
    elif input == 'aut1.leaves':
        return 11
    elif input == 'aut2.trans':
        return 12
    elif input == 'aut2.leaves':
        return 13
    # else:
    #     print(input)

def merge_json_files(file_list):
    merged_data = {}
    for file in file_list:
        with open(file, 'r') as f:
            data = json.load(f)
            for key, value in data.items():
                merged_data[key] = dict(sorted(value.items(), key=lambda item: compare_function(item[0])))
                # if key not in merged_data:
                #     merged_data[key] = {'q': value['q'], 'G': value['G'], 'G2': value['G2'], 't': [], 's': []}
                # merged_data[key]['t'].append(value['t'])
                # merged_data[key]['s'].append(value['s'])
    return merged_data

# Example usage
# sys.argv[1] = './feynopt/qcec.json'
name = sys.argv[1].split('/')[0] # [:-len('.json')].replace('/', '-') #split('/')[1] + '-' + sys.argv[1].split('/')[2].split('.')[0]
sys.argv.pop(0)
def json_to_latex_table(file_list, latex_filename):
    merged_data = merge_json_files(file_list)

    # Create the LaTeX table
    latex_code = """
\\documentclass{article}
\\usepackage{booktabs}
\\usepackage{geometry}
\\geometry{a4paper, paperwidth=50cm, paperheight=50cm, margin=1in}
\\begin{document}

\\begin{table}[h!]
\\centering
\\begin{tabular}{|l|c|c|c|""" + "c|" * len(list(next(iter(merged_data.items()))[1].keys())) + """}
\\hline
Filename & """ + " & ".join(list(next(iter(merged_data.items()))[1].keys())) + """ \\\\ \\hline
"""
# Filename & q & G & G2 & """ + " & ".join(f"t ({f.split('/')[1].split('.json')[0]}) & s ({f.split('/')[1].split('.json')[0]})" for f in file_list) + """ \\\\ \\hline
    merged_data = dict(sorted(merged_data.items(), key=lambda item: (item[0].split('_')[0], int(item[1]['q']))))
    for filename, values in merged_data.items():
        row = [filename.split('.qasm')[0]] + list(values.values())
        # , values['q'], values['G'], values['G2']]
        # for i in range(len(file_list)):
        #     row.append(values['t'][i] if i < len(values['t']) else '-')
        #     row.append(values['s'][i] if i < len(values['s']) else '-')
        latex_code += " & ".join(map(str, row)) + " \\\\ \\hline\n"

    latex_code += """
\\end{tabular}
\\""" + f"caption{{{str(os.getcwd()).split('/')[-1] + '/' + name}}}" + """
%label{table:your_label_here}
\\end{table}

\\end{document}
"""

    # Write the LaTeX code to a file
    latex_code = latex_code.replace('_', '\\_').replace('^', '\\^{}')
    with open(latex_filename, 'w') as file:
        file.write(latex_code)
json_to_latex_table(sys.argv, f'./tables/{name}.tex')
os.chdir('./tables')
os.system(f'pdflatex {name}.tex')
