# Author: Soeren Schulze, Uni Bremen 2012
# License: GPLv2 or higher, see LICENSE.txt
# Maintainer: s.schulze@uni-bremen.de

# A Makefile that keeps track of the successfully compiled COLORE files
# by generating .dummyclif files.

# ONLY TESTED WITH GNU MAKE

COLORE_PATH = colore

CLIF_EXCLUDES := \
colore/complex/dolce/dolce_hets/dolce_hets_tptp.clif \
colore/complex/process_specification_language/soo/psl-subset-519.clif \
colore/complex/process_specification_language/soo/soo.clif \
colore/complex/SUMO/sumo-cl.clif \
colore/core/mereological_geometry/cmmg.clif

CLIF_SOURCES := $(filter-out $(CLIF_EXCLUDES),$(shell find $(COLORE_PATH) -name \*.clif))
#XML_SOURCES := $(shell find $(COLORE_PATH) -name \*.xml)
# xml is currently not supported

all: clif

show_imports:
	@echo $(CLIF_IMPORTS)

%.dummyclif: %.clif
	hets $<
	touch $@

%.dummyxml: %.xml
	hets $<
	touch $@

clif: $(patsubst %.clif,%.dummyclif,$(CLIF_SOURCES))

xml: $(patsubst %.xml,%.dummyxml,$(XML_SOURCES))

clean:
	rm -f $(shell find $(COLORE_PATH) -name \*.dummy\*)
