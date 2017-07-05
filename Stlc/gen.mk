RULESFILE = stlc-rules.tex

all: stlc.pdf Stlc.v Stlc_inf.v

clean: paperclean

paperclean:
	rm -if *-rules.tex $(TOP).tex *.log ./*~ *.aux $(PDFS) *.bbl *.blg *.fdb_latexmk *.fls *.out *.nav


%.pdf : %.tex Makefile
	latexmk -bibtex -pdf $*.tex

$(RULESFILE): stlc.ott
	ott -i stlc.ott -o $(RULESFILE) \
          -tex_wrap false \
          -tex_show_meta false


%.tex: $(RULESFILE) %.mng Makefile
	ott -i stlc.ott \
                    -tex_wrap false \
                    -tex_show_meta false \
                    -tex_filter $*.mng $*.tex

Stlc.v: stlc.ott Makefile
	ott -i stlc.ott -o Stlc.v -coq_lngen true -coq_expand_list_types true
	make -f gen.mk METALIB.FIX_Stlc

Stlc_inf.v: stlc.ott Makefile
	lngen --coq-no-proofs --coq Stlc_inf.v --coq-ott Stlc stlc.ott
	make -f gen.mk METALIB.FIX_Stlc_inf

# Target to be called with some filename appended to it
# It is a quick hack to fix the imports to metalib
METALIB.FIX_%:
	sed -i -e 's/Metatheory/Metalib.Metatheory/g' $*.v
	sed -i -e 's/LibLNgen/Metalib.LibLNgen/g' $*.v
	sed '1d' $*.v > __TMP__; mv __TMP__ $*.v
