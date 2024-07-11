GOAL= itp2024
SLIDES= slides-itp2024
TARGET_MODULES= 
PREFIX= latex
TARGET_FILES= agdamacros.tex unicodeletters.tex macros.tex \
	1-introduction.tex 2-design-typing.tex 3-reference-implementation.tex \
	4-dynamic-logic.tex 5-semantics-and-soundness.tex 6-conclusion.tex \
	$(addprefix $(PREFIX)/, $(addsuffix .tex, $(TARGET_MODULES)))

ZIPGOAL= supplement-$(GOAL).zip

ARXIVGOAL= $(GOAL).zip

AGDATEX= ../../agdatex/agdatex.py
AGDAROOT= ../src
AGDAGENERATED= agda-generated.tex
AGDAFILES=  \
    00-All-Utilities.agda \
    01-Types.agda \
    02-Functions-Interpretations.agda \
    03-1-surface-syntax.agda \
    03-2-concrete-execution.agda \
    03-3-bigstep-execution.agda \
    11-abstract-representation-and-weakening.agda \
    11-1-examples.agda \
    12-2-abstract-execution-accessories-and-weakening.agda \
    13-2-abstract-Prog-state-execution.agda \
    14-2-abstract-Exec-state-execution.agda \
    21-2-Prog-state-modeling.agda \
    22-2-P-s-m-weakening.agda \
    23-2-prog-step-soundness.agda \
    24-2-Exec-state-modeling.agda \
    25-2-exec-step-soundness.agda

$(GOAL).pdf: $(GOAL).tex $(TARGET_FILES) $(PREFIX)/$(AGDAGENERATED)
	TEXINPUTS=$(PREFIX)/:$(TEXINPUTS) pdflatex --synctex=1 -interaction=nonstopmode -shell-escape $(GOAL)
	bibtex $(GOAL)
	TEXINPUTS=$(PREFIX)/:$(TEXINPUTS) pdflatex --synctex=1 -interaction=nonstopmode -shell-escape $(GOAL)

$(PREFIX)/%.tex: %.lagda
	agda --latex --only-scope-checking $<

supplement:
	rm -rf "__zip_cache"
	mkdir "__zip_cache"
	cp -r $(AGDAROOT)/* "__zip_cache/"
	sed -i '/^ *--!/d' "__zip_cache"/**/*.agda # Remove agdatex comments
	gawk -i inplace 'BEGIN{RS="";ORS="\n\n"}1' "__zip_cache"/**/*.agda # Replace tripple newlines with double newlines.
	rm "__zip_cache/StratF/SubstExamples.agda"
	rm __zip_cache/**/*.agdai
	cd __zip_cache && zip -r ../$(ZIPGOAL) *
	rm -rf "__zip_cache/"

$(ARXIVGOAL): $(GOAL).tex $(GOAL).bbl $(TARGET_FILES) acmart.cls agda.sty ACM-Reference-Format.bst
	zip $@ $^

$(SLIDES).pdf: $(SLIDES).tex $(TARGET_FILES)
	pdflatex  --synctex=1 -interaction=nonstopmode $(SLIDES)

.PHONY: all type-check clean $(ZIPGOAL)

all: $(GOAL).pdf $(ZIPGOAL)

### agdatex

$(PREFIX)/$(AGDAGENERATED): $(wildcard $(AGDAROOT)/*.agda)
	$(MAKE) runagdatex

## add  -v  for verbose output
runagdatex:
	$(AGDATEX) -r $(AGDAROOT) -e $(PREFIX)/$(AGDAGENERATED) -f $(addprefix $(AGDAROOT)/, $(AGDAFILES))
#	$(AGDATEX) -r $(AGDAROOT) -e $(PREFIX)/$(AGDAGENERATED) $(AGDAROOT)/*.agda

### clean up

clean:
	$(RM) -f *.agdai

### type checking

type-check:
	for src in $(addsuffix .lagda, $(TARGET_MODULES)) ; do \
		echo '***' checking $$src ; \
		agda $$src; \
	done
