.PHONY: test

test:
	raco test tests.rkt

doc:
	$(MAKE) -C document

clean:
	rm -f *~
	$(MAKE) -C document clean
