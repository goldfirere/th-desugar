# Migrating from `DLamE`/`DCaseE` to `DLamCasesE`

In `th-desugar-1.18`, the `DLamE` data constructor (for lambda expressions) and
`DCaseE` data constructor (for `case` expressions) are deprecated in favor of
the new `DLamCasesE` data constructor (for `\cases` expressions). This document
describes how one should migrate their code in anticipation of `DLamE` and
`DCaseE` being removed in a future `th-desugar`.

## What changed

The `DLamE` and `DCaseE` data constructors have been removed in favor of
`DLamCasesE`:

```diff
 data DExp
   = ...
-  | DLamE [Name] DExp
-  | DCaseE DExp [DMatch]
+  | DLamCasesE [DClause]
   | ...
```

That is, [`\cases`
expressions](https://downloads.haskell.org/ghc/9.10.1/docs/users_guide/exts/lambda_case.html)
(enabled by the `LambdaCase` language extension when using GHC 9.4 or later)
not only serves the role of `\cases`, but also the role of lambda expressions,
`case` expressions, and `\case` expressions, and `th-desugar` will desugar all
of these expressions to `DLamCasesE`. Note that `DLamCasesE` has the convention
that an empty list of `DClause`s implies a single argument, so `\case{}` will
desugar to `DLamCasesE []`.

This is a pretty large breaking change (even by `th-desugar` standards, so we
have made some effort to keep existing code involving `DLamE` and `DCaseE`
working until users have a chance to migrate. As such, `DLamE` and `DCaseE`
have been converted to pattern synonyms, although using these pattern synonyms
will incur deprecation warnings.

Some related changes that were brought on as a result of all this:

* The `mkDLamEFromDPats` function (which plays a similar role to `DLamE`) has
  also been deprecated.
* The `dsMatches` function no longer includes a `Name` argument for the variable
  being scrutinized, as this variable is not guaranteed to exist.

## Why did this change?

_(If you don't care about the motivations behind this change, feel free to skip
directly to the "Migrating your code" section below.)_

In previous versions of the library, `th-desugar` would desugar lambda
expressions, `\case` expressions, and `\cases` expressions to code that binds
arguments with a lambda and scrutinizes them using a `case` expression
involving a tuple. That is, given this code:

```hs
\(Identity x) (Identity y) -> x + y
```

`th-desugar` would desugar this to:

```hs
\arg1 arg2 ->
  case (arg1, arg2) of
    (Identity x, Identity y) -> x + y
```

This worked well enough, although it does require packing arguments into an
intermediate tuple. This was somewhat annoying (and potentially wasteful if GHC
did not optimize away the intermediate tuple), but not annoying enough to
invest in an alternative...

...that is, until recently. GHC 9.10 introduced two new language constructs:

* Embedded type patterns (e.g., `\(type a) (x :: a) -> x :: a`), enabled with
  the use of the
  [`RequiredTypeArguments`](https://downloads.haskell.org/ghc/9.10.1/docs/users_guide/exts/required_type_arguments.html)
  extension.
* Invisible type patterns (e.g., `\ @a (x :: a) -> x :: a`), enabled with the
  use of the
  [`TypeAbstractions`](https://downloads.haskell.org/ghc/9.10.1/docs/users_guide/exts/type_abstractions.html)
  extension with GHC 9.10 or later.

The important aspects of these language extensions are that they allow binding
types in patterns, and moreover, these types can only be used in certain
places. For example, GHC will reject code like `(type a, x)`. This is at odds
with the intermediate-tuple approach that `th-desugar` used previously, since
this means that given code like this:

```hs
\(type a) (x :: a) -> x :: a
```

A naïve attempt at desugaring the code would result in this:

```hs
\arg1 arg2 ->
  case (arg1, arg2) of
    (type a, x :: a) -> x :: a
```

But as mentioned above, GHC will reject this code! This proved quite
troublesome, and it would be non-trivial to adapt the intermediate-tuple
approach to allow these sorts of patterns (see the discussion on
[issue #204](https://github.com/goldfirere/th-desugar/issues/204) for more details).

Thankfully, there is a much more elegant solution that `th-desugar` can adopt:
desugar lambda, `case`, and `\case` expressions to `\cases`. This is because
embedded type patterns and invisible type patterns _can_ appear in the clauses
of a `\cases` expression, which allows `th-desugar` to support them without
needing special treatment. For example, given this code:

```hs
\(type a) (x :: a) -> x :: a
```

`th-desugar` will now desugar it to:

```hs
\cases (type a) (x :: a) -> x :: a
```

GHC will accept this code without issue. What's more, there is no longer a need
for any intermediate tuples, as `\cases` can scrutinize multiple arguments
without ever needing tuples.

An secondary benefit of this change is that the `DExp` data type is more
minimal. Rather than having separate constructs for binding names (`DLamE`) and
scrutinizing expressions (`DCaseE`), there is now a single construct
(`DLamCasesE`) that does both.

## Migrating your code

All uses of `DLamE` and `DCaseE` (which are now deprecated) should be migrated
over to `DLamCasesE` in anticipation of `DLamE`/`DCaseE` being removed in a
future GHC release. To make this process easier, `th-desugar` offers some
useful combinators for constructing `DLamCasesE` values that look like lambda
expressions, `case` expressions, or `\case` expressions:

* `dLamE :: [DPat] -> DExp -> DExp`: a lambda expression
* `dCaseE :: DExp -> [DMatch] -> DExp`: a `case` expression
* `dCasesE :: [DExp] -> [DClause] -> DExp`: a `case` expression that scrutinizes
  multiple arguments
* `dLamCaseE :: [DMatch] -> DExp`: a `\case` expression

If you use `DLamE` or `DCaseE` in an expression position, `dLamE` and `dCaseE`
offer nearly drop-in replacements. We say _nearly_ drop-in because the type of
`dLamE` is more general: it accepts a list of `DPat`s instead of a list of
`Name`s. As such, `DLamE vars rhs` can be converted to `dLamE (map DVarP names)
rhs`.

Note that as a result of all these changes, the `DMatch` data type is no longer
used directly in the `th-desugar` AST (only `DClause` is). Nevertheless, we
still keep `DMatch` around as it is a useful data type for the `dCaseE` and
`dLamCaseE` functions.

In addition to the changes above, you may need to make the following changes:

* Because the `mkDLamEFromDPats` function has been deprecated in favor of
  `dLamE`, any uses of `mkDLamEFromDPats pats rhs` should be replaced with
  `pure (dLamE pats rhs)`, which is an equivalent way of writing it.
* If you are using `dsMatches`, you will need to remove the `Name` argument,
  which represents a variable being scrutinized. The new approach that
  `th-desugar` uses to desugar `Match`es no longer requires this.

### Support for pre-9.4 versions of GHC

`\cases` is only available when using GHC 9.4 or later. As such, there is only
limited support for sweetening `DLamCasesE` values back to `template-haskell`
`Exp`s when using pre-9.4 versions of GHC. On these versions of GHC,
`th-desugar` recognizes the following special cases when sweetening
`DLamCasesE`:

* `DLamCasesE []` will be sweetened to `LamCaseE []`.
* `DLamCasesE [DClause pats rhs]` will be sweented to `LamE pats' rhs'` (where
  `pats'` and `rhs'` are the sweetened versions of `pats` and `rhs`,
  respectively).
* `DLamCasesE clauses` will be sweetened to `LamCaseE clauses'` (where
  `clauses'` is the sweetened version of `clauses`) when each clause in
  `clauses` has exactly one pattern.

If none of these cases apply, then `th-desugar` will raise an error when
sweetening the `DLamCasesE` value—at that point, your only course of action is
to rewrite the `DLamCasesE` value to something else or to upgrade GHC versions.
These special cases ensure that all lambda expressions, `case` expressions, and
`\case` expressions will successfully round-trip through a cycle of desugaring
and sweetening. That is, the only time that sweetening would error is if you
are desugaring a `\cases` expression that cannot trivially be rewritten to a
lambda, `case`, or `\case` expression.

### Anti-patterns to watch out for

Replacing `DLamE` and `DCaseE` expressions with `dLamE` and `dCase`,
respectively, will likely suffice to make your code work. That being said, it
may result in code that is unnecessarily verbose. For example, it was somewhat
common in previous `th-desugar` versions to write code that looks like this:

```hs
-- \name -> case name of pat -> rhs
DLamE [name] (DCaseE (DVarE name) (DMatch pat rhs))
```

A simple way to fix this code would be to instead write:

```hs
dLamE [DVarP name] (dCaseE (DVarE name) (DMatch pat rhs))
```

However, `th-desugar` would desugar this to:

```hs
\cases name -> (\cases pat -> rhs) name
```

Note that there are _two_ `\cases` expressions. This often wasteful, however,
as there is usually no need to bind `name` at all! Instead, if `name` does not
appear in `pat` or `rhs`, you can rewrite the code above as:

```hs
dLamCaseE (DMatch pat rhs)
```

`th-desugar` will desugar this code to:

```hs
\cases pat -> rhs
```

Which is much more concise.

A similar anti-pattern arises when binding multiple variables and scrutinizing
them as part of a tuple expression:

```hs
-- \name1 name2 -> case (name1, name2) of (pat1, pat2) -> rhs
DLamE [name1, name2] (DCaseE (mkTupleDExp [DVarE name1, DVarE name2]) (DMatch (mkTupleDPat [DVarP pat1, DVarP pat2]) rhs))
```

Once again, there is no need to explicitly bind `name1` or `name2` (assuming
that neither name appears in `pat` or `rhs`). The expression above can be more concisely
written as:

```hs
-- \cases pat1 pat2 -> rhs
DLamCasesE [DClause [DVarP pat1, DVarP pat2] rhs]
```

One of the advantages of using `\cases` as a primitive construct for pattern
matching is that we can avoid many uses of intermediate tuples like what is
seen above. You might as well take advantage of this!

### Example to follow

If you'd like to see an example of how to migrate a large library to work with
these changes, then
[singletons#595](https://github.com/goldfirere/singletons/pull/595) may be
useful.
