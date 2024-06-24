FILES= README.md \
    src/00-All-Utilities.agda \
    src/01-Types.agda \
    src/02-Functions-Interpretations.agda \
    src/03-1-surface-syntax.agda \
    src/03-2-concrete-execution.agda \
    src/03-3-bigstep-execution.agda \
    src/11-abstract-representation-and-weakening.agda \
    src/12-2-abstract-execution-accessories-and-weakening.agda \
    src/13-2-abstract-Prog-state-execution.agda \
    src/14-2-abstract-Exec-state-execution.agda \
    src/21-2-Prog-state-modeling.agda \
    src/22-2-P-s-m-weakening.agda \
    src/23-2-prog-step-soundness.agda \
    src/24-2-Exec-state-modeling.agda \
    src/25-2-exec-step-soundness.agda

artefact.zip: $(FILES)
	zip artefact.zip $(FILES)
