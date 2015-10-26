
SUBDIRS = Algebra Space Time

.PHONY: all clean $(SUBDIRS) 

all: $(SUBDIRS)

$(SUBDIRS): 
	$(MAKE) -C $@  check

Space: Algebra

Time: Algebra

clean:
	for d in $(SUBDIRS); do \
          $(MAKE) -C $$d cleaner; \
        done




# algebra: 
# 	$(MAKE) -C ./Algebra check

# space:
# 	$(MAKE) -C ./Space check

# time:
# 	$(MAKE) -C ./Time check


# clean-all: clean-algebra clean-space clean-time

# clean-algebra:
# 	$(MAKE) -C ./Algebra cleaner

# clean-space:
# 	$(MAKE) -C ./Space cleaner

# clean-time:
# 	$(MAKE) -C ./Time cleaner


sd




