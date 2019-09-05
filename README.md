This is a theoretical model for the linklets used in [Racket-on-Chez](https://blog.racket-lang.org/2018/01/racket-on-chez-status.html), for more info on the linklets, see `Flatt, Derici, Dybvig, Keep, Massaccesi, Spall, Tobin-Hochstadt, and Zeppieri, "Rebuilding Racket on Chez Scheme (Experience Report)"` ([pdf](https://www.cs.utah.edu/plt/publications/icfp19-rddkmstz.pdf)).

It includes a model for a subset of the [Fully Expanded Racket Programs](https://docs.racket-lang.org/reference/syntax-model.html?q=fully%20expanded#%28part._fully-expanded%29), namely `RC`, and a model for the linklets built on top of it, namely `Linklets`.

It tries to demonstrate what the linklets are and how they work.

To make sure everything works, just run `make test` on the top to run all the tests for both models.