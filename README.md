# A Dynamic Logic for Symbolic Execution for the Smart Contract Programming Language Michelson

Contents of the files

* 00-All-Utilities: utility functions for the `All` type
* 01-Types: encoding of Michelson types
* 02-Functions: encoding of Michelson instructions
* 03-1-surface-syntax: simplified definition of the surface syntax
  (for presentation only)
* 03-2-concrete-execution: definition of the execution environment,
  program execution, and contract execution
* 03-3-bigstep-execution: big-step semantics of Michelson, its
  soundness and completeness wrt semantics in concrete-execution
* 11-abstract-representation-and-weakening: self explanatory
* 11-1-examples: some examples from the paper
* 12-2-abstract-execution-accessories-and-weakening: self explanatory
* 13-2-abstract-Prog-state-execution: Michelson execution
* 14-2-abstract-Exec-state-execution: inter-contract execution
* 21-2-Prog-state-modeling: relation between concrete and abstract configurations
* 22-2-P-s-m-weakening: auxiliary
* 23-2-prog-step-soundness: soundness proof for Michelson execution
* 24-2-Exec-state-modeling: relation concrete/abstract at blockchain level
* 25-2-exec-step-soundness: soundness proof at blockchain level

This code runs with Agda version 2.6.4.3 and standard library version 2.0.
Everything except 03-1, 03-3, and 11-1 gets used by running

```
agda 25-2-exec-step-soundness.agda
```

The complete run takes about one minute on my machine.

