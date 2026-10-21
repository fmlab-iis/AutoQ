// Playground examples; `source` says where each one comes from.
export const EXAMPLES = [
  {
    "id": "readme",
    "title": "README example (2 qubits, X X H)",
    "source": "README.md (as on the landing page)",
    "mode": "ver",
    "files": [
      {
        "name": "pre.hsl",
        "content": "Extended Dirac\n{|00>, 1/2 |00> + 1/2 |01> + 1/2 |10> + 1/2 |11>}\n"
      },
      {
        "name": "circuit.qasm",
        "content": "OPENQASM 3;\ninclude \"stdgates.inc\";\nqubit[2] qb;\n\nx qb[0];\nx qb[1];\nh qb[1];\n"
      },
      {
        "name": "post.hsl",
        "content": "Extended Dirac\n{|10> - |11>, |10> + |00>}\n"
      }
    ]
  },
  {
    "id": "bv",
    "title": "Bernstein–Vazirani, 4 qubits",
    "source": "benchmarks/all/BV/03",
    "mode": "ver",
    "files": [
      {
        "name": "pre.hsl",
        "content": "Constants\nc1 := 1\nExtended Dirac\n{c1 |0000>}\n"
      },
      {
        "name": "circuit.qasm",
        "content": "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg qubits[4];\n\nh qubits[0];\nh qubits[1];\nh qubits[2];\nh qubits[3];\nz qubits[3];\ncx qubits[0], qubits[3];\ncx qubits[2], qubits[3];\nh qubits[0];\nh qubits[1];\nh qubits[2];\nh qubits[3];\n"
      },
      {
        "name": "post.hsl",
        "content": "Constants\nc1 := 1\nExtended Dirac\n{c1 |1011>}\n"
      }
    ]
  },
  {
    "id": "grover-sym",
    "title": "Grover search, symbolic amplitudes",
    "source": "benchmarks/all/GroverSym/02",
    "mode": "ver",
    "files": [
      {
        "name": "pre.hsl",
        "content": "Constants\nc1 := 1\nExtended Dirac\n{ c1 |000> }\n"
      },
      {
        "name": "circuit.qasm",
        "content": "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg qubits[3];\nx qubits[2];\n\nh qubits[0];\nh qubits[1];\nh qubits[2];\nx qubits[0];\nccx qubits[0], qubits[1], qubits[2];\nx qubits[0];\nh qubits[0];\nh qubits[1];\nx qubits[0];\nx qubits[1];\ncz qubits[0], qubits[1];\nx qubits[0];\nx qubits[1];\nh qubits[0];\nh qubits[1];\nh qubits[2];\n"
      },
      {
        "name": "post.hsl",
        "content": "Extended Dirac\n{pH |011> + pL ∑ |i|=3, i≠011 |i>}\nConstraints\nreal(pL) * real(pL) < 1/8\nimag(pL) = 0\nreal(pH) * real(pH) > 7/8\nimag(pH) = 0\n"
      }
    ]
  },
  {
    "id": "grover",
    "title": "Grover search, 5 qubits",
    "source": "benchmarks/all/Grover/03",
    "mode": "ver",
    "files": [
      {
        "name": "pre.hsl",
        "content": "Constants\nc1 := 1\nExtended Dirac\n{c1 |00000>}\n"
      },
      {
        "name": "circuit.qasm",
        "content": "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg qubits[5];\nx qubits[4];\n\nh qubits[0];\nh qubits[1];\nh qubits[2];\nh qubits[4];\n\nx qubits[0];\nx qubits[2];\nccx qubits[0], qubits[1], qubits[3];\ncz qubits[3], qubits[2];\nccx qubits[0], qubits[1], qubits[3];\nx qubits[0];\nx qubits[2];\nh qubits[0];\nh qubits[1];\nh qubits[2];\nx qubits[0];\nx qubits[1];\nx qubits[2];\nccx qubits[0], qubits[1], qubits[3];\ncz qubits[3], qubits[2];\nccx qubits[0], qubits[1], qubits[3];\nx qubits[0];\nx qubits[1];\nx qubits[2];\nh qubits[0];\nh qubits[1];\nh qubits[2];\nx qubits[4];\n\nx qubits[0];\nx qubits[2];\nccx qubits[0], qubits[1], qubits[3];\ncz qubits[3], qubits[2];\nccx qubits[0], qubits[1], qubits[3];\nx qubits[0];\nx qubits[2];\nh qubits[0];\nh qubits[1];\nh qubits[2];\nx qubits[0];\nx qubits[1];\nx qubits[2];\nccx qubits[0], qubits[1], qubits[3];\ncz qubits[3], qubits[2];\nccx qubits[0], qubits[1], qubits[3];\nx qubits[0];\nx qubits[1];\nx qubits[2];\nh qubits[0];\nh qubits[1];\nh qubits[2];\nx qubits[4];\n\nh qubits[4];\n"
      },
      {
        "name": "post.hsl",
        "content": "Constants\naH := 11 / (sqrt2 ^ 7)\naL := -1 / (sqrt2 ^ 7)\nExtended Dirac\n{aH |01001> + aL ∑ |i|=3, i≠010 |i01>}\n"
      }
    ]
  },
  {
    "id": "ifelse",
    "title": "Measurement and if",
    "source": "benchmarks/all/control_mini/if-else",
    "mode": "ver",
    "files": [
      {
        "name": "pre.hsl",
        "content": "Extended Dirac\n{|10>, |11>}\n"
      },
      {
        "name": "circuit.qasm",
        "content": "OPENQASM 3;\ninclude \"stdgates.inc\";\nqubit[2] qb;\nbit[2] outcome;\n\nh qb[0];\ncx qb[0], qb[1];\noutcome[0] = measure qb[0];\nif (!outcome[0]) {\n    x qb[0];\n}\n"
      },
      {
        "name": "post.hsl",
        "content": "Extended Dirac\n{|10>, |11>}\n"
      }
    ]
  },
  {
    "id": "while",
    "title": "While loop with an invariant",
    "source": "benchmarks/all/control_mini/while",
    "mode": "ver",
    "files": [
      {
        "name": "pre.hsl",
        "content": "Extended Dirac\n{|10>, |11>}\n"
      },
      {
        "name": "circuit.qasm",
        "content": "OPENQASM 3;\ninclude \"stdgates.inc\";\nqubit[2] qb;\nbit[2] outcome;\n\nh qb[0];\ncx qb[0], qb[1];\noutcome[0] = measure qb[0];\nwhile (!outcome[0]) { // loop-invariant.hsl\n    x qb[0];\n    h qb[0];\n    cx qb[0], qb[1];\n    outcome[0] = measure qb[0];\n}\n"
      },
      {
        "name": "post.hsl",
        "content": "Extended Dirac\n{|10>, |11>}\n"
      },
      {
        "name": "loop-invariant.hsl",
        "content": "Extended Dirac\n{|00> - |11>,\n |01> - |10>}\n"
      }
    ]
  },
  {
    "id": "eq",
    "title": "Equivalence: CX = H·CZ·H",
    "source": "landing page",
    "mode": "eq",
    "files": [
      {
        "name": "a.qasm",
        "content": "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg q[2];\ncx q[0], q[1];\n"
      },
      {
        "name": "b.qasm",
        "content": "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg q[2];\nh q[1];\ncz q[0], q[1];\nh q[1];\n"
      }
    ]
  },
  {
    "id": "eq-swap",
    "title": "Equivalence: SWAP = three CX gates",
    "source": "standard identity",
    "mode": "eq",
    "files": [
      {
        "name": "a.qasm",
        "content": "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg q[2];\nswap q[0], q[1];\n"
      },
      {
        "name": "b.qasm",
        "content": "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg q[2];\ncx q[0], q[1];\ncx q[1], q[0];\ncx q[0], q[1];\n"
      }
    ]
  },
  {
    "id": "eq-toffoli",
    "title": "Equivalence: Toffoli in Clifford+T",
    "source": "standard Clifford+T decomposition (7 T gates, 6 CX)",
    "mode": "eq",
    "files": [
      {
        "name": "a.qasm",
        "content": "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg q[3];\nccx q[0], q[1], q[2];\n"
      },
      {
        "name": "b.qasm",
        "content": "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg q[3];\nh q[2];\ncx q[1], q[2];\ntdg q[2];\ncx q[0], q[2];\nt q[2];\ncx q[1], q[2];\ntdg q[2];\ncx q[0], q[2];\nt q[1];\nt q[2];\nh q[2];\ncx q[0], q[1];\nt q[0];\ntdg q[1];\ncx q[0], q[1];\n"
      }
    ]
  },
  {
    "id": "eq-toffoli-bug",
    "title": "Non-equivalence: Toffoli with a wrong T gate",
    "source": "eq-toffoli with one T replaced by T†",
    "mode": "eq",
    "files": [
      {
        "name": "a.qasm",
        "content": "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg q[3];\nccx q[0], q[1], q[2];\n"
      },
      {
        "name": "b.qasm",
        "content": "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg q[3];\nh q[2];\ncx q[1], q[2];\ntdg q[2];\ncx q[0], q[2];\ntdg q[2]; // should be: t q[2];\ncx q[1], q[2];\ntdg q[2];\ncx q[0], q[2];\nt q[1];\nt q[2];\nh q[2];\ncx q[0], q[1];\nt q[0];\ntdg q[1];\ncx q[0], q[1];\n"
      }
    ]
  },
  {
    "id": "eq-phase",
    "title": "Equivalence up to global phase: XZ vs ZX",
    "source": "standard identity (XZ = −ZX)",
    "mode": "eq",
    "files": [
      {
        "name": "a.qasm",
        "content": "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg q[1];\nx q[0];\nz q[0];\n"
      },
      {
        "name": "b.qasm",
        "content": "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg q[1];\nz q[0];\nx q[0];\n"
      }
    ]
  }
];
