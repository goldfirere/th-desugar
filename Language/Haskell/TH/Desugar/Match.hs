{- Language/Haskell/TH/Desugar/Match.hs

(c) Richard Eisenberg 2013
eir@cis.upenn.edu

Simplifies case statements in desugared TH. After this pass, there are no
more overlapping or nested patterns.

This code is directly based on the analogous operation as written in GHC.
-}

module Language.Haskell.TH.Desugar.Match where

import Control.Applicative
import Control.Monad
import qualified Data.Set as S
import Language.Haskell.TH

import Language.Haskell.TH.Desugar.Core

scExp :: Quasi q => DExp -> q DExp
scExp (DAppE e1 e2) = DAppE <$> scExp e1 <*> scExp e2
scExp (DLamE names exp) = DLamE names <$> scExp exp
scExp (DCaseE scrut matches)
  | DVarE name <- scrut
  = simplCase [name] clauses
  | otherwise
  = do scrut_name <- newName "scrut"
       case_exp <- simplCase [scrut_name] clauses
       return $ DLetE [DValD (DVarP scrut_name) scrut] case_exp
  where
    clauses = map match_to_clause matches
    match_to_clause (DMatch pat exp) = DClause [pat] exp

scExp (DLetE decs body) = DLetE <$> mapM scLetDec decs <*> scExp body
scExp (DSigE exp ty) = DSigE <$> scExp exp <*> pure ty
scExp e = return e

scLetDec :: Quasi q => DLetDec -> q DLetDec
scLetDec (DFunD name clauses@(DClause pats1 _ : _)) = do
  arg_names <- mapM (const (newName "arg")) pats1
  case_exp <- simplCase arg_names clauses
  return $ DFunD name [DClause (map DVarP arg_names) case_exp]
scLetDec (DValD pat exp) = DValD pat <$> scExp exp
scLetDec dec = return dec

-- analogous to GHC's match (in deSugar/Match.lhs)
simplCase :: Quasi q
          => [Name]     -- the names of the scrutinees
          -> [DClause]  -- the matches (where the # of pats == length (1st arg))
          -> q DExp
simplCase vars@(v:_) clauses = do
  (aux_binds, tidy_clauses) <- mapAndUnzipM (tidyClause v) clauses
  let grouped = groupClauses tidy_clauses
  undefined

-- analogous to GHC's tidyEqnInfo
tidyClause :: Quasi q => Name -> DClause -> q (DExp -> DExp, DClause)
tidyClause _ (DClause [] _) =
  fail "Internal error in th-desugar: no patterns in tidyClause."
tidyClause v (DClause (pat : pats) body) = do
  (wrap, pat') <- tidy1 v pat
  return (wrap, DClause (pat' : pats) body)

tidy1 :: Quasi q
      => Name   -- the name of the variable that ...
      -> DPat   -- ... this pattern is matching against
      -> q (DExp -> DExp, DPat)   -- a wrapper and tidied pattern
tidy1 _ p@(DLitP {}) = return (id, p)
tidy1 v (DVarP var) = return (wrapBind var v, DWildP)
tidy1 _ p@(DConP {}) = return (id, p)
tidy1 v (DTildeP pat) = do
  sel_decs <- mkSelectorDecs pat v
  return (maybeDLetE sel_decs, DWildP)
tidy1 v (DBangP pat) =
  case pat of
    DLitP _   -> tidy1 v pat   -- already strict
    DVarP _   -> return (id, DBangP pat)  -- no change
    DConP _ _ -> tidy1 v pat   -- already strict
    DTildeP p -> tidy1 v (DBangP p) -- discard ~ under !
    DBangP p  -> tidy1 v (DBangP p) -- discard ! under !
    DWildP    -> return (id, DBangP pat)  -- no change
tidy1 _ DWildP = return (id, DWildP)
    
wrapBind :: Name -> Name -> DExp -> DExp
wrapBind new old
  | new == old = id
  | otherwise  = DLetE [DValD (DVarP new) (DVarE old)]

-- like GHC's mkSelectorBinds
-- RAE: change second param to Name?
mkSelectorDecs :: Quasi q
               => DPat      -- pattern to deconstruct
               -> Name      -- variable being matched against
               -> q [DLetDec]
mkSelectorDecs (DVarP v) name = return [DValD (DVarP v) (DVarE name)]
mkSelectorDecs pat name
  | S.null binders
  = return []

  | otherwise
  = do tuple_expr <- simplCase [name] [DClause [pat] local_tuple]
       tuple_var <- newName "tuple"
       projections <- mapM (mk_projection tuple_var) [0 .. tuple_size-1]
       return (DValD (DVarP tuple_var) tuple_expr : zipWith DValD (map DVarP binders_list) projections)

  where
    binders = extractBoundNamesDPat pat
    binders_list = S.toAscList binders
    tuple_size = length binders_list
    local_tuple = mkTupleDExp (map DVarE binders_list)

    mk_projection :: Quasi q
                  => Name   -- of the tuple
                  -> Int    -- which element to get (0-indexed)
                  -> q DExp
    mk_projection tup_name i = do
      var_name <- newName "proj"
      return $ DCaseE (DVarE tup_name) [DMatch (DConP (tupleDataName tuple_size) (mk_tuple_pats var_name i))
                                               (DVarE var_name)]

    mk_tuple_pats :: Name   -- of the projected element
                  -> Int    -- which element to get (0-indexed)
                  -> [DPat]
    mk_tuple_pats elt_name i = replicate i DWildP ++ DVarP elt_name : replicate (tuple_size - i - 1) DWildP

extractBoundNamesDPat :: DPat -> S.Set Name
extractBoundNamesDPat (DLitP _)      = S.empty
extractBoundNamesDPat (DVarP n)      = S.singleton n
extractBoundNamesDPat (DConP _ pats) = S.unions (map extractBoundNamesDPat pats)
extractBoundNamesDPat (DTildeP p)    = extractBoundNamesDPat p
extractBoundNamesDPat (DBangP p)     = extractBoundNamesDPat p
extractBoundNamesDPat DWildP         = S.empty

data PatGroup
  = PgAny         -- immediate match (wilds, vars, lazies)
  | PgCon Name 
  | PgLit Lit  
  | PgBang     

-- like GHC's groupEquations
groupClauses :: [DClause] -> [[(PatGroup, DClause)]]
groupClauses clauses
  = runs same_gp [(patGroup (firstPat clause), clause) | clause <- clauses]
  where
    same_gp :: (PatGroup, Clause) -> (PatGroup, Clause) -> Bool
    (pg1,_) `same_gp` (pg2,_) = pg1 `sameGroup` pg2

patGroup :: DPat -> PatGroup
patGroup (DLitP l)     = PgLit l
patGroup (DVarP {})    = error "Internal error in th-desugar (patGroup DVarP)"
patGroup (DConP con _) = PgCon con
patGroup (DTildeP {})  = error "Internal error in th-desugar (patGroup DTildeP)"
patGroup (DBangP {})   = PgBang
patGroup DWildP        = PgAny

firstPat :: DClause -> DPat
firstPat (DClause (pat : _) _) = pat
firstPat _ = error "Clause encountered with 

-- like GHC's runs
runs :: (a -> a -> Bool) -> [a] -> [[a]]
runs _ [] = []
runs p (x:xs) = case span (p x) xs of
                  (first, rest) -> (x:first) : (runs p rest)