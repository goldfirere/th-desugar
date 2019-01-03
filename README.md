`th-desugar` Package
====================

[![Hackage](https://img.shields.io/hackage/v/th-desugar.svg)](http://hackage.haskell.org/package/th-desugar)
[![Build Status](https://travis-ci.org/goldfirere/th-desugar.svg?branch=master)](https://travis-ci.org/goldfirere/th-desugar)

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

Known limitations
-----------------
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
