#!/usr/bin/python3
from datetime import timedelta
import json, os, re, sys

TIMEOUT = 300

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

# 新增：專門用來將兩個時間字串相加 (處理一般格式與 / 格式)
def add_time_strings(t1, t2):
    # 如果任一為非時間數值 (如 TIMEOUT, ERROR)，直接回傳該狀態
    if 'TIMEOUT' in str(t1) or 'TIMEOUT' in str(t2): return 'TIMEOUT'
    if 'ERROR' in str(t1) or 'ERROR' in str(t2): return 'ERROR'
    if '---' in str(t1) or '---' in str(t2): return '---'

    # 處理帶有 / 的情況 (例如 "1m/2m")
    if '/' in str(t1) or '/' in str(t2):
        p1 = str(t1).split('/')
        p2 = str(t2).split('/')
        # 確保長度一致，若無則補 0s (雖不常見但防呆)
        while len(p1) < 2: p1.append('0s')
        while len(p2) < 2: p2.append('0s')

        try:
            val1 = parse_duration(p1[0]) + parse_duration(p2[0])
            val2 = parse_duration(p1[1]) + parse_duration(p2[1])
            return f"{format_duration(val1)}/{format_duration(val2)}"
        except:
            return 'TIMEOUT'
    else:
        # 一般情況
        try:
            return format_duration(parse_duration(str(t1)) + parse_duration(str(t2)))
        except:
            return 'TIMEOUT'

# 新增：處理帶有 + 號的時間字串加總
def sum_plus_separated_values(value_str):
    if not isinstance(value_str, str) or '+' not in value_str:
        return value_str

    parts = value_str.split('+')
    sum_td = timedelta()
    sum_td_slash = timedelta() # 用於處理 / 後面的部分
    has_slash = False

    for part in parts:
        # 跳過非時間格式的字串
        if part in ['---', 'TIMEOUT', 'ERROR', '']:
            continue

        if '/' in part:
            has_slash = True
            try:
                p1, p2 = part.split('/')
                sum_td += parse_duration(p1)
                sum_td_slash += parse_duration(p2)
            except ValueError: pass
        else:
            try:
                sum_td += parse_duration(part)
            except ValueError: pass

    if has_slash:
        return format_duration(sum_td) + '/' + format_duration(sum_td_slash)
    return format_duration(sum_td)

def compare_function(input):
    if 'BVall' in input:
        return 1
    elif 'GHZall' in input:
        return 2
    elif 'GroverAll' in input:
        return 3
    elif 'GroverIterAll' in input:
        return 4
    elif 'MCToffoli' in input:
        return 5

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
    elif input == 'result2':
        return 11
    # else:
    #     print(input)

def compare_function3(input):
    if 'hsl' in input: return 0
    if 'cav23' in input: return 1

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

    contents = dict()
    tool_list_sorted = sorted(tool_list, key=lambda val: compare_function3(val))

    for file, datas in merged_data.items():
        the_string_to_be_added = ''
        first_tool = True

        for tool_path in tool_list_sorted:
            if tool_path not in datas:
                if not first_tool:
                    # 注意：因為合併了欄位，這裡的 placeholder 也要從 4 個減為 3 個
                    the_string_to_be_added += ' & - & - & -'
                continue
            data = datas[tool_path].copy()

            # 1. 先處理 + 號加總 (既有邏輯)
            for key in ['read_file_time', 'total', 'result']:
                if key in data:
                    data[key] = sum_plus_separated_values(data[key])

            # 移除不需要的 key (既有邏輯)
            for k in ['before_state', 'before_trans', 'after_state', 'after_trans']:
                if k in data: del data[k]

            # --- [核心修改開始] ---
            # 2. 將 total 與 result 相加存回 total，並刪除 result
            if 'total' in data and 'result' in data:
                # 使用上面定義的 add_time_strings
                data['total'] = add_time_strings(data['total'], data['result'])
                del data['result'] # <--- 刪除 result key
            # --- [核心修改結束] ---

            # 3. 計算 result2 (Grand Total)
            # 因為 result 已經被加進 total 並刪除了，這裡只需要加 read_file_time + total
            if '/' in str(data.get('total', '')):
                # 處理 / 分隔的情況
                t_parts = data['total'].split('/')
                r_val = parse_duration(data.get('read_file_time', '0s'))

                v1 = r_val + parse_duration(t_parts[0])
                v2 = r_val + parse_duration(t_parts[1])
                data['result2'] = format_duration(v1) + '/' + format_duration(v2)
            else:
                # 一般情況
                val_read = parse_duration(data.get('read_file_time', '0s'))
                val_total = parse_duration(str(data.get('total', '0s')))
                # 不用再加 data['result'] 了，因為已經 merged 進 total
                data['result2'] = format_duration(val_read + val_total)

            # 處理 Timeout
            if ('TIMEOUT' in str(data.get('read_file_time', '')) or
                'TIMEOUT' in str(data.get('total', '')) or
                parse_duration(data['result2'].split('/')[0] if '/' in data['result2'] else data['result2']).total_seconds() > TIMEOUT):

                data['read_file_time'] = r'\multicolumn{3}{c}{\TO}' # <--- 修改：跨欄數改為 3 (因為欄位變少了)
                if 'total' in data: del data['total']
                if 'result2' in data: del data['result2']
            else:
                data['result2'] = r'\textbf{' + data['result2'] + r'}'

            # 產生表格字串
            if first_tool:
                sorted_data = dict(sorted(data.items(), key=lambda item: compare_function2(item[0])))
                # replace logic handles ERROR formatting
                the_string_to_be_added += (' & ' + ' & '.join(map(str, list(sorted_data.values())))).replace('ERROR', r'\error')
                first_tool = False
            else:
                sorted_data = dict(sorted(data.items(), key=lambda item: compare_function2(item[0])))
                tool_values = list(sorted_data.values())
                # 跳過 q 和 G，保留 read_file_time, total (已合併), result2
                tool_values_without_qg = tool_values[2:]
                the_string_to_be_added += (' & ' + ' & '.join(map(str, tool_values_without_qg))).replace('ERROR', r'\error')

        the_string_to_be_added = the_string_to_be_added.replace('TIMEOUT', r'\TO')

        key_name = file.split('/')[1]
        if key_name not in contents:
            contents[key_name] = the_string_to_be_added + '\\\\\n'
        else:
            contents[key_name] += the_string_to_be_added + '\\\\\n'

    # --- [LaTeX 模板修改] ---
    # 必須減少欄位定義與 multicolumn 的寬度
    latex_code = r'''\documentclass{article}

\usepackage{booktabs}
\usepackage{xspace}
\usepackage{multicol}
\usepackage{multirow}
\usepackage{graphicx}
\usepackage{colortbl}
\usepackage{xcolor}
\usepackage{tabularx}

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
\newcommand{\mctoffolibench}[0]{\small\textsc{MCToffoli}\xspace}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}%\pagenumbering{gobble}

%\scalebox{0.01}
{%\hspace{-100pt}
\hoffset=-1in
\voffset=-1in
\setbox0\hbox{
\newcolumntype{Y}{>{\raggedleft\arraybackslash}X}
\begin{tabularx}{\textwidth}{c YY YYY YYY}
\toprule
  & \multirow{2}{*}{\textbf{\#q}} & \multirow{2}{*}{\textbf{\#G}} & \multicolumn{3}{c}{This Work} & \multicolumn{3}{c}{CAV'23} \\
  \cmidrule(lr){4-6} \cmidrule(lr){7-9}
  & & & \multicolumn{1}{c}{trans} & \multicolumn{1}{c}{ver} & \multicolumn{1}{c}{total} & \multicolumn{1}{c}{trans} & \multicolumn{1}{c}{ver} & \multicolumn{1}{c}{total} \\
\midrule
  \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\bvmultbench}}
''' + contents['BVall'] + r'''\midrule
  \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\ghzmultbench}}
''' + contents['GHZall'] + r'''\midrule
  \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\grovermultbench}}
''' + contents['GroverAll'] + r'''\midrule
  \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\oegroverbench}}
''' + contents['GroverIterAll'] + r'''\midrule
  \multirow{ 5}{*}{\rotatebox[origin=c]{90}{\mctoffolibench\footnotemark}}
''' + contents['MCToffoli'] + r'''\bottomrule
\end{tabularx}
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
sysargv1 = 'correct/hsl.json'
name = sysargv1.split('/')[0] # [:-len('.json')].replace('/', '-') #split('/')[1] + '-' + sysargv1.split('/')[2].split('.')[0]
# sys.argv.pop(0)
if not os.path.exists('tables'):
   os.makedirs('tables')
json_to_latex_table(['./correct/hsl.json', './correct/cav23.json'], f'./tables/{name}.tex')
os.chdir('./tables')
os.system(f'pdflatex {name}.tex && vips copy {name}.pdf[dpi=600] {name}.jpg')

# https://tex.stackexchange.com/questions/299005/automatic-page-size-to-fit-arbitrary-content
