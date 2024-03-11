GOAL= itp2024
SLIDES= slides-itp2024
TARGET_MODULES= 
TARGET_FILES= agdamacros.tex unicodeletters.tex \
	1-introduction.tex 2-design-typing.tex 3-reference-implementation.tex \
	4-dynamic-logic.tex 5-semantics-and-soundness.tex 6-conclusion.tex \
	$(addprefix $(PREFIX)/, $(addsuffix .tex, $(TARGET_MODULES)))
PREFIX= latex

ZIPGOAL= supplement-$(GOAL).zip

ARXIVGOAL= $(GOAL).zip

AGDATEX= ../../agdatex/agdatex.py
AGDAROOT= ../src
AGDAGENERATED= agda-generated.tex

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

$(PREFIX)/$(AGDAGENERATED):
	$(MAKE) runagdatex

runagdatex:
	$(AGDATEX) -v -r $(AGDAROOT) -e $(PREFIX)/$(AGDAGENERATED) $(AGDAROOT)/*.agda

### clean up

clean:
	$(RM) -f *.agdai

### type checking

type-check:
	for src in $(addsuffix .lagda, $(TARGET_MODULES)) ; do \
		echo '***' checking $$src ; \
		agda $$src; \
	done
