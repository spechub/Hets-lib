# Variables

files := $(wildcard *.casl)
files += $(filter-out %pp.dol,$(wildcard *.dol))


# List of libraries that make problems
ignore_files = DRA.casl DRA.dol DRA_FO.casl FlipFlop.casl Modal_RCC8.dol PA2.dol
files := $(filter-out $(ignore_files),$(files))

clean_files := $(wildcard *.thy *.patch *.env *.pp.dol)


# Implicit rules

%.env : %.casl 
	@echo -----------------------------------------------
	@echo "Check library: $<"	
	hets -o env $< 
	@echo "Checked: $<"	
	@echo -----------------------------------------------

%.env : %.dol 
	@echo -----------------------------------------------
	@echo "Check library: $<"	
	hets -o env $< 
	@echo "Checked: $<"	
	@echo -----------------------------------------------


# targets

all: cleanest check

print: 
	@echo $(files)


check: $(files)
	$(MAKE) $(files:%.casl=%.env) $(files:%.dol=%.env) 


clean: 
ifneq "$(strip $(CLEAN_FILES))" ""
	mv -b $(CLEAN_FILES) ../.tmp
endif


cleaner: clean
ifneq "$(strip $(CLEANER_FILES))" ""
	mv -b $(CLEANER_FILES) ../.tmp
endif

cleanest: cleaner


.phony: all check clean cleaner cleanest 
