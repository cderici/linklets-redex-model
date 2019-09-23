.PHONY: test paper

all: test paper

test:
	raco test tests.rkt

paper:
	$(MAKE) -C paper all

doc:
	$(MAKE) -C document

clean-doc:
	$(MAKE) -C document clean

clean: clean-doc
	$(RM) *~
	$(MAKE) -C paper clean
