-----------------------------------------------------------------------------
-- |
-- Module      :  Language.Haskell.TH.Desugar.Lift
-- Copyright   :  (C) 2014 Richard Eisenberg
-- License     :  BSD-style (see LICENSE)
-- Maintainer  :  Ryan Scott
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Historically, this module defined orphan @Lift@ instances for the data types
-- in @th-desugar@. Nowadays, these instances are defined alongside the data
-- types themselves, so this module simply re-exports the instances.
--
----------------------------------------------------------------------------

module Language.Haskell.TH.Desugar.Lift () where

import Language.Haskell.TH.Desugar ()
