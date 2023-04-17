#!/usr/bin/python3
import sys
from mqt import qcec

root = sys.argv[1]
result = qcec.verify(f"{root}/bug.qasm", f"{root}/spec.qasm")
print(result.equivalence, flush=True)