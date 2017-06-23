Stlc.v: stlc.ott Makefile
	ott -i stlc.ott -o Stlc.v -coq_lngen true -coq_expand_list_types false
	make METALIB.FIX_Stlc

Stlc_inf.v: stlc.ott Makefile
	lngen --coq Stlc_inf.v --coq-ott Stlc stlc.ott
	make METALIB.FIX_Stlc_inf

%.vo : %.v
	coqc $*.v

# Target to be called with some filename appended to it
# It is a quick hack to fix the imports to metalib
METALIB.FIX_%:
	sed -i -e 's/Metatheory/Metalib.Metatheory/g' $*.v
	sed -i -e 's/LibLNgen/Metalib.LibLNgen/g' $*.v
	sed '1d' $*.v > __TMP__; mv __TMP__ $*.v
