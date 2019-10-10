.PHONY: test paper

all: test paper

test:
	$(MAKE) -C test all

paper:
	$(MAKE) -C paper all
	cp paper/linklets.pdf .

doc:
	$(MAKE) -C document

clean-doc:
	$(MAKE) -C document clean

clean: clean-doc
	$(RM) *~ linklets.pdf
	$(MAKE) -C paper clean
