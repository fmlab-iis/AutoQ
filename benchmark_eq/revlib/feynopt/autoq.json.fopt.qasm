Unrecognized option "revlib/qasms/autoq.json"
Feynman -- quantum circuit toolkit
Written by Matthew Amy

Run with feynopt [passes] (<circuit>.(qc | qasm) | Small | Med | All | -benchmarks <path to folder>)

Options:
  -purecircuit	Perform qasm passes assuming the initial state (of qubits) is unknown

Transformation passes:
  -inline	Inline all sub-circuits
  -mctExpand	Expand all MCT gates using |0>-initialized ancillas
  -toCliffordT	Expand all gates to Clifford+T gates

Optimization passes:
  -simplify	Basic gate-cancellation pass
  -phasefold	Merges phase gates according to the circuit's phase polynomial
  -statefold	Slightly more powerful phase folding
  -tpar		Phase folding+T-parallelization algorithm from [AMM14]
  -cnotmin	Phase folding+CNOT-minimization algorithm from [AAM17]
  -clifford		 Re-synthesize Clifford segments
  -O2		**Standard strategy** Phase folding+simplify
  -O3		Phase folding+state folding+simplify

Verification passes:
  -verify	Perform verification algorithm of [A18] after all passes

E.g. "feyn -verify -inline -cnotmin -simplify circuit.qc" will first inline the circuit,
       then optimize CNOTs, followed by a gate cancellation pass and finally verify the result

WARNING: Using "-verify" with "All" may crash your computer without first setting
         user-level memory limits. Use with caution
