{- Language/Haskell/TH/Desugar/Util.hs

(c) Richard Eienberg 2013
eir@cis.upenn.edu

Utility functions for th-desugar package.
-}

module Language.Haskell.TH.Desugar.Util where

import Language.Haskell.TH
import Data.List

-- | Reify a declaration, warning the user about splices if the reify fails. The warning
-- says that reification can fail if you try to reify a type in the same splice as it is
-- declared.
reifyWithWarning :: Name -> Q Info
reifyWithWarning name = recover
  (fail $ "Looking up " ++ (show name) ++ " in the list of available " ++
        "declarations failed.\nThis lookup fails if the declaration " ++
        "referenced was made in the same Template\nHaskell splice as the use " ++
        "of the declaration. If this is the case, put\nthe reference to " ++
        "the declaration in a new splice.")
  (reify name)

-- | Report that a certain TH construct is impossible
impossible :: String -> Q a
impossible err = fail (err ++ "\nThis should not happen in Haskell.\nPlease email eir@cis.upenn.edu with your code if you see this.")

-- | Extract the @TyVarBndr@s and constructors given the @Name@ of a type
getDataD :: String       -- ^ Print this out on failure
         -> Name         -- ^ Name of the datatype (@data@ or @newtype@) of interest
         -> Q ([TyVarBndr], [Con])
getDataD error name = do
  info <- reifyWithWarning name
  dec <- case info of
           TyConI dec -> return dec
           _ -> badDeclaration
  case dec of
    DataD _cxt _name tvbs cons _derivings -> return (tvbs, cons)
    NewtypeD _cxt _name tvbs con _derivings -> return (tvbs, [con])
    _ -> badDeclaration
  where badDeclaration =
          fail $ "The name (" ++ (show name) ++ ") refers to something " ++
                 "other than a datatype. " ++ error

-- | From the name of a data constructor, retrieve its definition as a @Con@
dataConNameToCon :: Name -> Q Con
dataConNameToCon con_name = do
  -- we need to get the field ordering from the constructor. We must reify
  -- the constructor to get the tycon, and then reify the tycon to get the `Con`s
  info <- reifyWithWarning con_name
  type_name <- case info of
                 DataConI _name _type parent_name _fixity -> return parent_name
                 _ -> impossible "Non-data-con used to construct a record."
  (_, cons) <- getDataD "This seems to be an error in GHC." type_name
  let m_con = find ((con_name ==) . get_con_name) cons
  case m_con of
    Just con -> return con
    Nothing -> impossible "Datatype does not contain one of its own constructors."

  where
    get_con_name (NormalC name _)  = name
    get_con_name (RecC name _)     = name
    get_con_name (InfixC _ name _) = name
    get_con_name (ForallC _ _ con) = get_con_name con

-- | Extracts the name out of a variable pattern, or returns @Nothing@
stripVarP_maybe :: Pat -> Maybe Name
stripVarP_maybe (VarP name) = Just name
stripVarP_maybe _           = Nothing

-- | Extracts the name out of a @PlainTV@, or returns @Nothing@
stripPlainTV_maybe :: TyVarBndr -> Maybe Name
stripPlainTV_maybe (PlainTV n) = Just n
stripPlainTV_maybe _           = Nothing