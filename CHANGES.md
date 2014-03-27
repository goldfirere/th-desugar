Version 1.3.1
-------------
* Update cabal file to include testing files in sdist.

Version 1.3.0
-------------
* Update to work with `type Pred = Type` in GHC 7.9. This changed the
`DPred` type for all GHC versions, though.

Version 1.2.0
-------------
* Generalized interface to allow any member of the `Qausi` class, instead of
  just `Q`.

Version 1.1.1
-------------
* Made compatible with HEAD after change in role annotation syntax.

Version 1.1
-----------
* Added module `Language.Haskell.TH.Desugar.Expand`, which allows for expansion
  of type synonyms in desugared types.
* Added `Show`, `Typeable`, and `Data` instances to desugared types.
* Fixed bug where an as-pattern in a `let` statement was scoped incorrectly.
* Changed signature of `dsPat` to be more specific to as-patterns; this allowed
  for fixing the `let` scoping bug.
* Created new functions `dsPatOverExp` and `dsPatsOverExp` to allow for easy
  desugaring of patterns.
* Changed signature of `dsLetDec` to return a list of `DLetDec`s.
* Added `dsLetDecs` for convenience. Now, instead
  of using `mapM dsLetDec`, you should use `dsLetDecs`.

Version 1.0
-----------

* Initial release