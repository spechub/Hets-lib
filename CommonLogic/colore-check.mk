# Author: Soeren Schulze, Uni Bremen 2012
# License: GPLv2 or higher, see LICENSE.txt
# Maintainer: s.schulze@uni-bremen.de

# A Makefile that keeps track of the successfully compiled COLORE files
# by generating .dummyclif files.

# ONLY TESTED WITH GNU MAKE

COLORE_PATH = colore

CLIF_EXCLUDES := colore/complex/dolce/dolce_hets/dolce_hets_tptp.clif \
colore/complex/dolce/dolce_original/dolce_mereology.clif \
colore/complex/dolce/dolce_original/dolce_present.clif \
colore/complex/dolce/dolce_original/dolce_temporary_parthood.clif \
colore/complex/dolce/dolce_psl/dolce_present_convex.clif

CLIF_SOURCES := $(filter-out $(CLIF_EXCLUDES),$(shell find $(COLORE_PATH) -name \*.clif))
#XML_SOURCES := $(shell find $(COLORE_PATH) -name \*.xml)
# xml is currently not supported

CLIF_IMPORTS := $(shell ls -1d $(foreach src,$(CLIF_SOURCES),         \
                                             $(shell dirname $(src))) \
                        | sort | uniq | paste -s -d ':')

all: clif

show_imports:
	@echo $(CLIF_IMPORTS)

%.dummyclif: %.clif
	@echo "hets -L [...] $<"
	@hets -L $(CLIF_IMPORTS) $<
	touch $@

%.dummyxml: %.xml
	hets $<
	touch $@

clif: $(patsubst %.clif,%.dummyclif,$(CLIF_SOURCES))

xml: $(patsubst %.xml,%.dummyxml,$(XML_SOURCES))

clean:
	rm -f $(shell find $(COLORE_PATH) -name \*.dummy\*)
