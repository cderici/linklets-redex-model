.PHONY: test

test:
	raco test tests.rkt

clean:
	rm -f *~
