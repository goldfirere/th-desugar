Version 1.4.1
-------------
* Added `Language.Haskell.TH.Desugar.Lift`, which provides `Lift` instances
for all of the th-desugar types.

* Added `applyDExp` and `applyDType` as convenience functions.

Version 1.4.0
-------------
* All `Dec`s can now be desugared, to the new `DDec` type.

* Sweetening `Dec`s that do not exist in GHC 7.6.3- works on a "best effort" basis:
closed type families are sweetened to open ones, and role annotations are dropped.

* `Info`s can now be desugared. Desugaring takes into account GHC bug #8884, which
meant that reifying poly-kinded type families in GHC 7.6.3- was subtly wrong.

* There is a new function `flattenDValD` which takes a binding like
  `let (a,b) = foo` and breaks it apart into separate assignments for `a` and `b`.

* There is a new `Desugar` class with methods `desugar` and `sweeten`. See
the documentation in `Language.Haskell.TH.Desugar`.

* Variable names that are distinct in desugared code are now guaranteed to
have distinct answers to `nameBase`.

* Added a new function `getRecordSelectors` that extracts types and definitions
of record selectors from a datatype definition.

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
