#!/root/AutoQ/py/bin/python
qasm = """OPENQASM 3.0;
include "stdgates.inc";
qubit[${n}] qb;
bit[${n}] outcome;

% for i in range(n):
h qb[${i}];
% endfor

% for i in range(1, (n+1)//2):
cz qb[${2*i-1}], qb[${2*i}];
% endfor

% for i in range(n//2):
cz qb[${2*i}], qb[${2*i+1}];
% endfor

% for i in range(n//2):
h qb[${2*i+1}];
% endfor

% for i in range(n//2):
outcome[${2*i+1}] = measure qb[${2*i+1}];
if (!outcome[${2*i+1}]) {
    cx qb[${2*i+1}], qb[${2*i+2}];
}
else {
    cx qb[${2*i+1}], qb[${2*i+2}];
    x qb[${2*i+1}];
}

% endfor
% for i in range((n - 1) // 2):
cx qb[${2*i+2}], qb[${2*i+1}];
% endfor
"""

if __name__ == "__main__":
    import sys
    import math
    from mako.template import Template
    match sys.argv:
        case [_, n] if n.isdigit() and int(n) >= 3:
            result = Template(text=qasm).render(n=(n_val:=int(n)), math=math)
            print(result, end="")
        case _:
            raise ValueError("Usage: python circuit.qasm.mako.py <n>")