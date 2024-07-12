FILES= README.md \
    src/00-All-Utilities.agda \
    src/01-Types.agda \
    src/02-Functions-Interpretations.agda \
    src/03-1-surface-syntax.agda \
    src/03-2-concrete-execution.agda \
    src/03-3-bigstep-execution.agda \
    src/11-abstract-representation-and-weakening.agda \
    src/11-1-examples.agda \
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

PAPERFILES= \
	tex/1-introduction.tex \
	tex/2-design-typing.tex \
	tex/3-reference-implementation.tex \
	tex/4-dynamic-logic.tex \
	tex/5-semantics-and-soundness.tex \
	tex/6-conclusion.tex \
	tex/agdamacros.tex \
	tex/cc-by.pdf \
	tex/ecoop2024.bib \
	tex/itp2024.aux \
	tex/itp2024.bbl \
	tex/itp2024.blg \
	tex/itp2024.log \
	tex/itp2024.out \
	tex/itp2024.pdf \
	tex/itp2024.ptb \
	tex/itp2024.rel \
	tex/itp2024.tex \
	tex/itp2024.vtc \
	tex/lipics-logo-bw.pdf \
	tex/lipics-v2021.cls \
	tex/macros.tex \
	tex/orcid.pdf \
	tex/unicodeletters.tex \
	tex/bib/refs.bib \
	tex/latex/00-All-Utilities.tex \
	tex/latex/01-Types.tex \
	tex/latex/02-Functions-Interpretations.tex \
	tex/latex/03-1-surface-syntax.tex \
	tex/latex/03-2-concrete-execution.tex \
	tex/latex/03-3-bigstep-execution.tex \
	tex/latex/03-concrete-execution.tex \
	tex/latex/11-1-examples.tex \
	tex/latex/11-abstract-representation-and-weakening.tex \
	tex/latex/12-2-abstract-execution-accessories-and-weakening.tex \
	tex/latex/13-2-abstract-Prog-state-execution.tex \
	tex/latex/14-2-abstract-Exec-state-execution.tex \
	tex/latex/21-2-Prog-state-modeling.tex \
	tex/latex/22-2-P-s-m-weakening.tex \
	tex/latex/23-2-prog-step-soundness.tex \
	tex/latex/24-2-Exec-state-modeling.tex \
	tex/latex/25-1-exec-step-soundness.tex \
	tex/latex/25-2-exec-step-soundness.tex \
	tex/latex/agda-generated.tex \
	tex/latex/agda.sty \
	tex/figures/SyntaxInstruction.png \
	tex/figures/SyntaxOverloading.png \
	tex/figures/SyntaxProgram.png \
	tex/figures/TypesSemantics.png \
	tex/figures/TypesType.png


ecoop2024.zip: $(PAPERFILES)
	zip ecoop2024.zip $(PAPERFILES)
