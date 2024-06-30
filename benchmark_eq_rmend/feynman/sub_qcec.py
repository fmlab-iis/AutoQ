#!/usr/bin/python3
import sys
from mqt import qcec

result = qcec.verify(sys.argv[1], sys.argv[2], nthreads=1)
print('{' + f"'result': '{result.equivalence}'" + '}', flush=True)