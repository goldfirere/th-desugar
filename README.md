`th-desugar` Package
====================

This package provides the `Language.Haskell.TH.Desugar` module, which desugars
Template Haskell's rich encoding of Haskell syntax into a simpler encoding.
This desugaring discards surface syntax information (such as the use of infix
operators) but retains the original meaning of the TH code. The intended use
of this package is as a preprocessor for more advanced code manipulation
tools. Note that the input to any of the `ds...` functions should be produced
from a TH quote, using the syntax `[| ... |]`. If the input to these functions
is a hand-coded TH syntax tree, the results may be unpredictable. In
particular, it is likely that promoted datatypes will not work as expected.

The package was designed for use with the `singletons` package, so some design
decisions are based on that use case, when more than one design choice was
possible.

I will try to keep this package up-to-date with respect to changes in GHC.