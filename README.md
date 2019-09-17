This is a theoretical model for the linklets used in [Racket-on-Chez](https://blog.racket-lang.org/2018/01/racket-on-chez-status.html), and [Pycket](https://github.com/pycket/pycket). For more info on the linklets, see `"Rebuilding Racket on Chez Scheme (Experience Report)"` ([pdf](https://www.cs.utah.edu/plt/publications/icfp19-rddkmstz.pdf)).

It includes a model for a subset of the [Fully Expanded Racket Programs](https://docs.racket-lang.org/reference/syntax-model.html?q=fully%20expanded#%28part._fully-expanded%29), namely `RC`, and a model for the linklets built on top of it, namely `Linklets`.

It tries to demonstrate what the linklets are and how they work.

#### some make targets for use (on the top)

* `make test` : to make sure everything works, runs all the tests in the `tests.rkt`
* `make doc` : to make `document/document.pdf`
* `make clean` : to clean up things
