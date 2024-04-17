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

## Limited support for embedded types in patterns

In GHC 9.10 or later, the `RequiredTypeArguments` language extension allows one
to write definitions with embedded types in patterns, e.g.,

```hs
idv :: forall a -> a -> a
idv (type a) = id @a
```

`th-desugar` supports writing patterns like `(type a)` via the `DTypeP` data
constructor of `DPat`. Be warned, however, that `th-desugar` only supports
desugaring `DTypeP` in the clauses of function declarations, such as the
declaration of `idv` above. As a result, `th-desugar` does not support
desugaring `DTypeP` in any other position, including:

* Lambda expressions. For example, the following is not supported:

  ```hs
  idv2 :: forall a -> a -> a
  idv2 = \(type a) -> id @a
  ```
* `\case` expressions. For example, the following is not supported:

  ```hs
  idv3 :: forall a -> a -> a
  idv3 = \case
    (type a) -> id @a
  ```
* `\cases` expressions. For example, the following is not supported:

  ```hs
  idv4 :: forall a -> a -> a
  idv4 = \cases
    (type a) x -> x :: a
  ```

Note that all of the example above use an explicit `type` keyword, but the same
considerations apply for embedded type patterns that do not use the `type`
keyword. That is, `th-desugar` supports desugaring the following:

```hs
idv' :: forall a -> a -> a
idv' a = id @a
```

But `th-desugar` does not support desugaring any of the following:

```hs
idv2' :: forall a -> a -> a
idv2' = \a -> id @a

idv3' :: forall a -> a -> a
idv3' = \case
  a -> id @a

idv4' :: forall a -> a -> a
idv4' = \cases
  a x -> x :: a
```

As a workaround, one can convert uses of lambdas and `LambdaCase` to function
declarations, which are fully supported. See also [this `th-desugar`
issue](https://github.com/goldfirere/th-desugar/issues/210), which proposes a
different approach to desugaring that would allow all of the examples above to
be accepted.

## Limited support for invisible type patterns

In GHC 9.10 or later, the `TypeAbstractions` language extension allows one to
write definitions with invisible type patterns, e.g.,

```hs
f :: a -> a
f @a = id @a
```

`th-desugar` supports writing patterns like `@a` via the `DInvisP` data
constructor of `DPat`. Be warned, however, that `th-desugar` only supports
desugaring `DInvisP` in the clauses of function declarations, such as the
declaration of `f` above. As a result, `th-desugar` does not support desugaring
`DInvisP` in any other position, such as lambda expressions or `\cases`
expressions.

Ultimately, this limitation has the same underlying cause as `th-desugar`'s
limitations surrounding embedded types in patterns (see the "Limited support
for embedded types in patterns" section above). As a result, the same
workaround applies: convert uses of lambdas and `LambdaCase` to function
declarations, which are fully supported.
