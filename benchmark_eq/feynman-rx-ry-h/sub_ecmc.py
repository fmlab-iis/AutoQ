#!/usr/bin/python3

import sys; sys.path.insert(0, '/home/alan23273850/Quokka-Sharp/quokka_sharp')
import quokka_sharp as qk
import sys

def main(tool_path, qasmfile1, qasmfile2):

    # Parse the circuit
    circuit1 = qk.encoding.QASMparser(qasmfile1, True)
    # Parse another circuit
    circuit2 = qk.encoding.QASMparser(qasmfile2, True)
    # Get (circuit1)^dagger(circuit2)
    circuit2.dagger()
    circuit1.append(circuit2)
    # Get CNF for the merged circuit
    cnf = qk.encoding.QASM2CNF(circuit1)
    res = qk.CheckEquivalence(tool_path, cnf)


    print("{'result': '" + ("T" if res else "F") + "'}")


if __name__ == '__main__':
    if len(sys.argv) < 2:
        main("/home/alan23273850/GPMC/bin/gpmc -mode=1", "test.qasm", "test.qasm")
    else:
        tool_path = "/home/alan23273850/GPMC/bin/gpmc -mode=1" #sys.argv[1]
        circ1 = sys.argv[1]
        circ2 = sys.argv[2]
        main(tool_path, circ1, circ2)
