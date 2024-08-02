`th-desugar` Package
====================

[![Hackage](https://img.shields.io/hackage/v/th-desugar.svg)](http://hackage.haskell.org/package/th-desugar)
[![Build Status](https://github.com/goldfirere/th-desugar/workflows/Haskell-CI/badge.svg)](https://github.com/goldfirere/th-desugar/actions?query=workflow%3AHaskell-CI)

This package provides the `Language.Haskell.TH.Desugar` module, which desugars
Template Haskell's rich encoding of Haskell syntax into a simpler encoding.
This desugaring discards surface syntax information (such as the use of infix
operators) but retains the original meaning of the TH code. The intended use
of this package is as a preprocessor for more advanced code manipulation
tools. Note that the input to any of the `ds...` functions should be produced
from a TH quote, using the syntax `[| ... |]`. If the input to these functions
is a hand-coded TH syntax tree, the results may be unpredictable. In
particular, it is likely that promoted datatypes will not work as expected.

One explicit goal of this package is to reduce the burden of supporting multiple
GHC / TH versions. Thus, the desugared language is the same across all GHC versions,
and any inconsistencies are handled internally.

The package was designed for use with the `singletons` package, so some design
decisions are based on that use case, when more than one design choice was
possible.

I will try to keep this package up-to-date with respect to changes in GHC.
The minimum supported version of GHC is 8.0, which was chosen to avoid various
Template Haskell bugs in older GHC versions that affect how this library
desugars code. If this choice negatively impacts you, please submit a bug
report.

Known limitations
-----------------

## Desugaring depends on language extensions of use sites

Suppose you quote some Template Haskell declarations in module `A`:

```hs
{-# LANGUAGE ... #-}
module A where

decs :: Q [Dec]
decs = [d| ... |]
```

And later desugar the declarations with `th-desugar` in module `B`:

```hs
{-# LANGUAGE ... #-}
module B where

import A (decs)
import Language.Haskell.TH.Desugar (dsDecs)

$(do desugaredDecs <- dsDecs decs
     ...)
```

There are some situations where `th-desugar`'s desugaring depends on which
language extensions are enabled, such as:

* `MonadFailDesugaring` (for desugaring partial pattern matches in `do`
  notation)
* `NoFieldSelectors` (for determining if a record field can be reified as a
  field selector with `lookupValueNameWithLocals`)

Somewhat counterintuitively, `th-desugar` will consult the language extensions
in module `B` (the site where the `decs` are used) for this process, not module
`A` (where the `decs` were defined). This is really a Template Haskell
limitation, since Template Haskell does not offer any way to reify which
language extensions were enabled at the time the declarations were defined. As a
result, `th-desugar` can only check for language extensions at use sites.

## Limited support for kind inference

`th-desugar` sometimes has to construct types for certain Haskell entities.
For instance, `th-desugar` desugars all Haskell98-style constructors to use
GADT syntax, so the following:

```haskell
data T (a :: k) = MkT (Proxy a)
```

Will be desugared to something like this:

```haskell
data T (a :: k) where
  MkT :: forall k (a :: k). Proxy a -> T (a :: k)
```

Notice that `k` is explicitly quantified in the type of `MkT`. This is due to
an additional pass that `th-desugar` performs over the type variable binders
of `T` to extract all implicitly quantified variables and make them explicit.
This makes the desugared types forwards-compatible with a
[future version of GHC](https://github.com/goldfirere/ghc-proposals/blob/bbefbee6fc0cddb10bbacc85f79e66c2706ce13f/proposals/0000-no-kind-vars.rst)
that requires all kind variables in a top-level `forall` to be explicitly
quantified.

This process of extracting all implicitly quantified kind variables is not
perfect, however. There are some obscure programs that will cause `th-desugar`
to produce type variable binders that are ill scoped. Here is one example:

```haskell
data P k (a :: k)
data Foo (a :: Proxy j) (b :: k) c = MkFoo c (P k j)
```

If you squint hard at `MkFoo`, you'll notice that `j :: k`. However, this
relationship is not expressed _syntactically_, which means that `th-desugar`
will not be aware of it. Therefore, `th-desugar` will desugar `Foo` to:

```haskell
data Foo (a :: Proxy j) (b :: k) c where
  MkFoo :: forall j k (a :: Proxy j) (b :: k) c.
           c -> P k j -> Foo (a :: Proxy j) (b :: k) c
```

This is incorrect since `k` must come before `j` in order to be well scoped.
There is a workaround to this issue, however: add more explicit kind
information. If you had instead written this:

```haskell
data Foo (a :: Proxy (j :: k)) (b :: k) c = MkFoo c (P k j)
```

Then the fact that `j :: k` is expressed directly in the AST, so `th-desugar`
is able to pick up on it and pick `forall k j (a :: Proxy j) (b :: k) c. <...>`
as the telescope for the type of `MkFoo`.

The following constructs are known to be susceptible to this issue:

1. Desugared Haskell98-style constructors
2. Locally reified class methods
3. Locally reified record selectors
4. Locally reified data constructors
5. Locally reified type family instances (on GHC 8.8 and later, in which the
   Template Haskell AST supports explicit `foralls` in type family equations)

## Limited support for linear types

Currently, the `th-desugar` AST deliberately makes it impossible to represent
linear types, and desugaring a linear function arrow will simply turn into a
normal function arrow `(->)`. This choice is partly motivated by issues in the
way that linear types interact with Template Haskell, which sometimes make it
impossible to tell whether a reified function type is linear or not. See, for
instance, [GHC#18378](https://gitlab.haskell.org/ghc/ghc/-/issues/18378).

## Limitations of support for desugaring guards

`th-desugar` supports guards in the sense that it will desugar guards to
equivalent code that instead uses `case` expressions. For example, this code:

```hs
f (x, y)
  | x == "hello" = x
  | otherwise = y
```

Will be desugared to this code:

```hs
f arg =
  case arg of
    (x, y) ->
      case x2 == "hello" of
        True  -> x
        False -> y
```

This has the advantage that it saves users from needing to care about the
complexities of guards. It does have some drawbacks, however, which we describe
below.

### Desugaring guards can result in quadratic code size

If you desugar this program involving guards:

```hs
data T = A Int | B Int | C Int

f :: T -> T -> Maybe Int
f (A x1) (A x2)
  | x1 == x2
  = Just x1
f (B x1) (B x2)
  | x1 == x2
  = Just x1
f (C x1) (C x2)
  | x1 == x2
  = Just x1
f _ _ = Nothing
```

You will end up with:

```hs
f :: T -> T -> Maybe Int
f arg1 arg2 =
  case (# arg1, arg2 #) of
    (# A x1, A x2 #) ->
      case x1 == x2 of
        True ->
          Just x1
        False ->
          case (# arg1, arg2 #) of
            (# B y1, B y2 #) ->
              case y1 == y2 of
                True ->
                  Just y1
                False ->
                  case (# arg1, arg2 #) of
                    (# C z1, C z2 #) ->
                      case z1 == z2 of
                        True ->
                          Just z1
                        False ->
                          case (# arg1, arg2 #) of
                            (# _, _ #) ->
                              Nothing
                    (# _, _ #) ->
                      Nothing
            (# C y1, C y2 #) ->
              case y1 == y2 of
                True ->
                  Just y1
                False ->
                  case (# arg1, arg2 #) of
                    (# _, _ #) ->
                      Nothing
            (# _, _ #) ->
              Nothing
    (# B x1, B x2 #) ->
      case x1 == x2 of
        True ->
          Just x1
        False ->
          case (# arg1, arg2 #) of
            (# C y1, C y2 #) ->
              case y1 == y2 of
                True ->
                  Just y1
                False ->
                  case (# arg1, arg2 #) of
                    (# _, _ #) ->
                      Nothing
            (# _, _ #) ->
              Nothing
    (# C x1, C x2 #) ->
      case x1 == x2 of
        True ->
          Just x1
        False ->
          case (# arg1, arg2 #) of
            (# _, _ #) ->
              Nothing
    (# _, _ #) ->
      Nothing
```

That is signficantly more code. In the worst case, the algorithm that
`th-desugar` uses for desugaring guards can lead to a quadratic increase in
code size. One way to avoid this is avoid having incomplete guards that fall
through to later clauses. That is, if you rewrite the original code to this:

```hs
f :: T -> T -> Maybe Int
f (A x1) (A x2)
  | x1 == x2
  = Just x1
  | otherwise
  = Nothing
f (B x1) (B x2)
  | x1 == x2
  = Just x1
  | otherwise
  = Nothing
f (C x1) (C x2)
  | x1 == x2
  = Just x1
  | otherwise
  = Nothing
```

Then `th-desugar` will desugar it to:

```hs
f :: T -> T -> Maybe Int
f arg1 arg2 =
  case (# arg1, arg2 #) of
    (# A x1, A x2 #) ->
      case x1 == x2 of
        True ->
          Just x1
        False ->
          Nothing
    (# B x1, B x2 #) ->
      case x1 == x2 of
        True ->
          Just x1
        False ->
          Nothing
    (# C x1, C x2 #) ->
      case x1 == x2 of
        True ->
          Just x1
        False ->
          Nothing
```

This code, while still more verbose than the original, uses a constant amount
of extra code per clause.

### Desugaring guards can produce more warnings than the original code

The approach that `th-desugar` uses to desugar guards can result in code that
produces GHC compiler warnings (if `-fenable-th-splice-warnings` is enabled)
where the original code does not. For example, consider the example from above:

```hs
data T = A Int | B Int | C Int

f :: T -> T -> Maybe Int
f (A x1) (A x2)
  | x1 == x2
  = Just x1
f (B x1) (B x2)
  | x1 == x2
  = Just x1
f (C x1) (C x2)
  | x1 == x2
  = Just x1
f _ _ = Nothing
```

This code compiles without any GHC warnings. If you desugar this code using
`th-desugar`, however, it will produce these warnings:

```
warning: [-Woverlapping-patterns]
    Pattern match is redundant
    In a case alternative: (# B y1, B y2 #) -> ...
   |
   |             (# B y1, B y2 #) ->
   |             ^^^^^^^^^^^^^^^^^^^...

warning: [-Woverlapping-patterns]
    Pattern match is redundant
    In a case alternative: (# C y1, C y2 #) -> ...
   |
   |             (# C y1, C y2 #) ->
   |             ^^^^^^^^^^^^^^^^^^^...

warning: [-Woverlapping-patterns]
    Pattern match is redundant
    In a case alternative: (# C y1, C y2 #) -> ...
   |
   |             (# C y1, C y2 #) ->
   |             ^^^^^^^^^^^^^^^^^^^...
```

GHC is correct here: these matches are wholly redundant. `th-desugar` could
potentially recognize this and perform a more sophisticated analysis to detect
and remove such matches when desugaring guards, but it currently doesn't do
such an analysis.

## No support for view patterns

`th-desugar` does not support desugaring view patterns. An alternative to using
view patterns in the patterns of a function is to use pattern guards.
Currently, there is not a viable workaround for using view patterns in pattern
synonym definitions—see [this `th-desugar`
issue](https://github.com/goldfirere/th-desugar/issues/174).

## No support for or-patterns

`th-desugar` does not support desugaring
[or-patterns](https://github.com/ghc-proposals/ghc-proposals/blob/c9401f037cb22d1661931b2ec621925101052997/proposals/0522-or-patterns.rst).
See [this `th-desugar`
issue](https://github.com/goldfirere/th-desugar/issues/232).

## No support for `ApplicativeDo`

`th-desugar` does not take the `ApplicativeDo` extension into account when
desugaring `do` notation. For example, if you desugar this:

```hs
{-# LANGUAGE ApplicativeDo #-}

f x y = do
  x' <- x
  y' <- y
  return (x' ++ y')
```

Then `th-desugar` will translate the uses of `<-` in the `do` block to uses of
`Monad` operations (e.g., `(>>=)`) rather than `Applicative` operations (e.g.,
`(<*>)`). See [this `th-desugar`
issue](https://github.com/goldfirere/th-desugar/issues/138).

## No support for `RecursiveDo`

`th-desugar` does not support the `RecursiveDo` extension at all, so it cannot
desugar any uses of `mdo` expressions or `rec` statements.

## No support for unresolved infix operators

`th-desugar` does not support desugaring unresolved infix operators, such as
`UInfixE`. You are unlikely to encounter this limitation when dealing with
Template Haskell quotes, since quoted infix operators will translate to uses of
`InfixE` rather than `UInfixE`. Rather, this limitation would only be
encountered if you manually construct a Template Haskell `Exp` using `UInfixE`.
