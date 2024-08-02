{- Language/Haskell/TH/Desugar/Match.hs

(c) Richard Eisenberg 2013
rae@cs.brynmawr.edu

Simplifies case statements in desugared TH. After this pass, there are no
more nested patterns.

This code is directly based on the analogous operation as written in GHC.
-}

{-# LANGUAGE CPP, TemplateHaskellQuotes #-}

module Language.Haskell.TH.Desugar.Match (scExp, scLetDec) where

import Prelude hiding ( fail, exp )

import Control.Monad hiding ( fail )
import qualified Control.Monad as Monad
import Data.Data
import qualified Data.Foldable as F
import Data.Generics
import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Set as S
import qualified Data.Map as Map
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax

import Language.Haskell.TH.Desugar.AST
import Language.Haskell.TH.Desugar.Core (dsReify, maybeDLetE, mkTupleDExp)
import Language.Haskell.TH.Desugar.FV
import qualified Language.Haskell.TH.Desugar.OSet as OS
import Language.Haskell.TH.Desugar.Util
import Language.Haskell.TH.Desugar.Reify

-- | Remove all nested pattern-matches within this expression. This also
-- removes all 'DTildePa's and 'DBangPa's. After this is run, every pattern
-- is guaranteed to be either a 'DConPa' with bare variables as arguments,
-- a 'DLitPa', or a 'DWildPa'.
scExp :: DsMonad q => DExp -> q DExp
scExp (DAppE e1 e2) = DAppE <$> scExp e1 <*> scExp e2
scExp (DLamCasesE clauses) = do
  -- Per the Haddocks for DLamCasesE, an empty list of clauses indicates that
  -- the overall `\cases` expression takes one argument. Otherwise, we look at
  -- the first clause to see how many arguments the expression takes, as each
  -- clause is required to have the same number of patterns.
  let num_args =
        case clauses of
          [] -> 1
          DClause pats _ : _ -> length pats
  clause' <- scClauses num_args clauses
  pure $ DLamCasesE [clause']
scExp (DLetE decs body) = DLetE <$> mapM scLetDec decs <*> scExp body
scExp (DSigE exp ty) = DSigE <$> scExp exp <*> pure ty
scExp (DAppTypeE exp ty) = DAppTypeE <$> scExp exp <*> pure ty
scExp (DTypedBracketE exp) = DTypedBracketE <$> scExp exp
scExp (DTypedSpliceE exp) = DTypedSpliceE <$> scExp exp
scExp (DForallE tele exp) = DForallE tele <$> scExp exp
scExp (DConstrainedE cxt exp) = DConstrainedE <$> mapM scExp cxt <*> scExp exp
scExp e@(DVarE {}) = return e
scExp e@(DConE {}) = return e
scExp e@(DLitE {}) = return e
scExp e@(DStaticE {}) = return e
scExp e@(DTypeE {}) = return e

-- | Like 'scExp', but for a 'DLetDec'.
scLetDec :: DsMonad q => DLetDec -> q DLetDec
scLetDec (DFunD name clauses) = do
  -- `DFunD`s are expected to have a non-empty list of clauses where each clause
  -- has a number of patterns equal to the number of arguments.
  let num_args =
        case clauses of
          [] -> error $ "The `" ++ nameBase name ++
                        "` function has no clauses -- should never happen"
          DClause pats _ : _ -> length pats
  clause' <- scClauses num_args clauses
  pure $ DFunD name [clause']
scLetDec (DValD pat exp) = DValD pat <$> scExp exp
scLetDec (DPragmaD prag) = DPragmaD <$> scLetPragma prag
scLetDec dec@(DSigD {}) = return dec
scLetDec dec@(DInfixD {}) = return dec

-- | Convert a list of 'DClause's into a single 'DClause', where the right-hand
-- side of the output 'DClause' matches on all of the patterns of the input
-- 'DClause's without using nested pattern matching.
scClauses ::
     DsMonad q
  => Int -- ^ The number of arguments in each 'DClause'.
  -> [DClause] -> q DClause
scClauses num_args clauses = do
  arg_names <- replicateM num_args (newUniqueName "_arg")
  clauses' <- mapM sc_clause_rhs clauses
  case_exp <- simplCaseExp arg_names clauses'
  pure $ DClause (map DVarP arg_names) case_exp
  where
    sc_clause_rhs (DClause pats exp) = DClause pats <$> scExp exp

scLetPragma :: DsMonad q => DPragma -> q DPragma
scLetPragma = topEverywhereM scExp -- Only topEverywhereM because scExp already recurses on its own

type MatchResult = DExp -> DExp

matchResultToDExp :: MatchResult -> DExp
matchResultToDExp mr = mr failed_pattern_match
  where
    failed_pattern_match = DAppE (DVarE 'error)
                                 (DLitE $ StringL "Pattern-match failure")

simplCaseExp :: DsMonad q
             => [Name]
             -> [DClause]
             -> q DExp
simplCaseExp vars clauses =
  do let eis = [ EquationInfo (to_ne_pats pats) (\_ -> rhs) |
                 DClause pats rhs <- clauses ]
     matchResultToDExp `liftM` simplCase vars eis
  where
    to_ne_pats :: [DPat] -> NonEmpty DPat
    to_ne_pats pats =
      case pats of
        p:ps -> p:|ps
        [] -> error "Clause encountered with no patterns -- should never happen"

data EquationInfo = EquationInfo (NonEmpty DPat) MatchResult  -- like DClause, but with a hole

-- analogous to GHC's match (in deSugar/Match.lhs)
simplCase :: DsMonad q
          => [Name]         -- the names of the scrutinees
          -> [EquationInfo] -- the matches (where the # of pats == length (1st arg))
          -> q MatchResult
simplCase [] clauses = return (foldr1 (.) match_results)
  where
    match_results = [ mr | EquationInfo _ mr <- clauses ]
simplCase (v:vs) clauses = do
  (aux_binds, tidy_clauses) <- mapAndUnzipM (tidyClause v) clauses
  let grouped = groupClauses tidy_clauses
  match_results <- match_groups grouped
  return (adjustMatchResult (foldr (.) id aux_binds) $
          foldr1 (.) match_results)
  where
    match_groups :: DsMonad q => [NonEmpty (PatGroup, EquationInfo)] -> q [MatchResult]
    match_groups [] = matchEmpty v
    match_groups gs = mapM match_group gs

    match_group :: DsMonad q => NonEmpty (PatGroup, EquationInfo) -> q MatchResult
    match_group eqns@((group,_) :| _) =
      case group of
        PgCon _ -> matchConFamily vars $ subGroup [(c,e) | (PgCon c, e) <- NE.toList eqns]
        PgLit _ -> matchLiterals  vars $ subGroup [(l,e) | (PgLit l, e) <- NE.toList eqns]
        PgBang  -> matchBangs     vars $ drop_group eqns
        PgAny   -> matchVariables vars $ drop_group eqns

    drop_group :: NonEmpty (PatGroup, EquationInfo) -> NonEmpty EquationInfo
    drop_group = fmap snd

    vars = v:|vs

-- analogous to GHC's tidyEqnInfo
tidyClause :: DsMonad q => Name -> EquationInfo -> q (DExp -> DExp, EquationInfo)
tidyClause v (EquationInfo (pat :| pats) body) = do
  (wrap, pat') <- tidy1 v pat
  return (wrap, EquationInfo (pat' :| pats) body)

tidy1 :: DsMonad q
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
    DConP{}   -> tidy1 v pat   -- already strict
    DTildeP p -> tidy1 v (DBangP p) -- discard ~ under !
    DBangP p  -> tidy1 v (DBangP p) -- discard ! under !
    DSigP p _ -> tidy1 v (DBangP p) -- discard sig under !
    DWildP    -> return (id, DBangP pat)  -- no change
    DTypeP _  -> return (id, DBangP pat)  -- no change
    DInvisP _ -> return (id, DBangP pat)  -- no change
tidy1 v (DSigP pat ty)
  | no_tyvars_ty ty = tidy1 v pat
  -- The match-flattener doesn't know how to deal with patterns that mention
  -- type variables properly, so we give up if we encounter one.
  -- See https://github.com/goldfirere/th-desugar/pull/48#issuecomment-266778976
  -- for further discussion.
  | otherwise = Monad.fail
    "Match-flattening patterns that mention type variables is not supported."
  where
    no_tyvars_ty :: Data a => a -> Bool
    no_tyvars_ty = everything (&&) (mkQ True no_tyvar_ty)

    no_tyvar_ty :: DType -> Bool
    no_tyvar_ty (DVarT{}) = False
    no_tyvar_ty t         = gmapQl (&&) True no_tyvars_ty t
tidy1 _ DWildP = return (id, DWildP)
tidy1 _ (DTypeP ty) = return (id, DTypeP ty)
tidy1 _ (DInvisP ty) = return (id, DInvisP ty)

wrapBind :: Name -> Name -> DExp -> DExp
wrapBind new old
  | new == old = id
  | otherwise  = DLetE [DValD (DVarP new) (DVarE old)]

-- | Desugar a lazy pattern that bind multiple variables to code that extracts
-- fields from tuples. For instance, this:
--
-- @
-- data Pair a b = MkPair a b
--
-- f :: Pair a b -> Pair b a
-- f ~(MkPair x y) = MkPair y x
-- @
--
-- Desugars to this (roughly) when match-flattened:
--
-- @
-- f :: Pair a b -> Pair b a
-- f p =
--   let tuple = case p of
--                 MkPair x y -> (x, y)
--
--       x = case tuple of
--             (x, _) -> x
--
--       y = case tuple of
--             (_, y) -> x
--
--    in MkPair y x
-- @
--
-- This takes heavy inspiration from GHC's own @mkSelectorBinds@ function.
mkSelectorDecs :: DsMonad q
               => DPat      -- pattern to deconstruct
               -> Name      -- variable being matched against
               -> q [DLetDec]
mkSelectorDecs (DVarP v) name = return [DValD (DVarP v) (DVarE name)]
mkSelectorDecs pat name
  | OS.null binders
  = return []

  | [binder] <- F.toList binders
  = do val_var <- newUniqueName "var"
       err_var <- newUniqueName "err"
       bind    <- mk_bind val_var err_var binder
       return [DValD (DVarP val_var) (DVarE name),
               DValD (DVarP err_var) (DVarE 'error `DAppE`
                                       (DLitE $ StringL "Irrefutable match failed")),
               bind]

  | otherwise
  = do tuple_expr <- simplCaseExp [name] [DClause [pat] local_tuple]
       tuple_var <- newUniqueName "tuple"
       projections <- mapM (mk_projection tuple_var) [0 .. tuple_size-1]
       return (DValD (DVarP tuple_var) tuple_expr :
               zipWith DValD (map DVarP binders_list) projections)

  where
    binders = extractBoundNamesDPat pat
    binders_list = F.toList binders
    tuple_size = length binders_list
    local_tuple = mkTupleDExp (map DVarE binders_list)

    mk_projection :: DsMonad q
                  => Name   -- of the tuple
                  -> Int    -- which element to get (0-indexed)
                  -> q DExp
    mk_projection tup_name i = do
      var_name <- newUniqueName "proj"
      return $ dCaseE (DVarE tup_name) [DMatch (DConP (tupleDataName tuple_size) [] (mk_tuple_pats var_name i))
                                               (DVarE var_name)]

    mk_tuple_pats :: Name   -- of the projected element
                  -> Int    -- which element to get (0-indexed)
                  -> [DPat]
    mk_tuple_pats elt_name i = replicate i DWildP ++ DVarP elt_name : replicate (tuple_size - i - 1) DWildP

    mk_bind scrut_var err_var bndr_var = do
      rhs_mr <- simplCase [scrut_var] [EquationInfo (pat:|[]) (\_ -> DVarE bndr_var)]
      return (DValD (DVarP bndr_var) (rhs_mr (DVarE err_var)))

data PatGroup
  = PgAny         -- immediate match (wilds, vars, lazies)
  | PgCon Name
  | PgLit Lit
  | PgBang

-- like GHC's groupEquations
groupClauses :: [EquationInfo] -> [NonEmpty (PatGroup, EquationInfo)]
groupClauses clauses
  = NE.groupBy same_gp [(patGroup (firstPat clause), clause) | clause <- clauses]
  where
    same_gp :: (PatGroup, EquationInfo) -> (PatGroup, EquationInfo) -> Bool
    (pg1,_) `same_gp` (pg2,_) = pg1 `sameGroup` pg2

patGroup :: DPat -> PatGroup
patGroup (DLitP l)       = PgLit l
patGroup (DVarP {})      = error "Internal error in th-desugar (patGroup DVarP)"
patGroup (DConP con _ _) = PgCon con
patGroup (DTildeP {})    = error "Internal error in th-desugar (patGroup DTildeP)"
patGroup (DBangP {})     = PgBang
patGroup (DSigP{})       = error "Internal error in th-desugar (patGroup DSigP)"
patGroup DWildP          = PgAny
patGroup (DTypeP {})     = PgAny
patGroup (DInvisP {})    = PgAny

sameGroup :: PatGroup -> PatGroup -> Bool
sameGroup PgAny     PgAny     = True
sameGroup PgBang    PgBang    = True
sameGroup (PgCon _) (PgCon _) = True
sameGroup (PgLit _) (PgLit _) = True
sameGroup _         _         = False

-- Precondition: the input list contains at least one element.
subGroup :: Ord a => [(a, EquationInfo)] -> NonEmpty (NonEmpty EquationInfo)
subGroup group
  = case map NE.reverse $ Map.elems $ foldl accumulate Map.empty group of
      e:es -> e:|es
      [] -> error "Internal error in th-desugar (subGroup)"
  where
    accumulate pg_map (pg, eqn)
      = case Map.lookup pg pg_map of
          Just eqns -> Map.insert pg (NE.cons eqn eqns) pg_map
          Nothing   -> Map.insert pg (eqn :| [])        pg_map

firstPat :: EquationInfo -> DPat
firstPat (EquationInfo (pat :| _) _) = pat

data CaseAlt = CaseAlt { alt_con  :: Name         -- con name
                       , _alt_args :: [Name]       -- bound var names
                       , _alt_rhs  :: MatchResult  -- RHS
                       }

-- from GHC's MatchCon.lhs
matchConFamily :: DsMonad q => NonEmpty Name -> NonEmpty (NonEmpty EquationInfo) -> q MatchResult
matchConFamily (var:|vars) groups
  = do alts <- mapM (matchOneCon vars) groups
       mkDataConCase var alts

-- like matchOneConLike from MatchCon
matchOneCon :: DsMonad q => [Name] -> NonEmpty EquationInfo -> q CaseAlt
matchOneCon vars eqns@(eqn1 :| _)
  = do arg_vars <- selectMatchVars (pat_args pat1)
       match_result <- match_group arg_vars

       return $ CaseAlt (pat_con pat1) arg_vars match_result
  where
    pat1 = firstPat eqn1

    pat_args (DConP _ _ pats) = pats
    pat_args _                = error "Internal error in th-desugar (pat_args)"

    pat_con (DConP con _ _) = con
    pat_con _               = error "Internal error in th-desugar (pat_con)"

    match_group :: DsMonad q => [Name] -> q MatchResult
    match_group arg_vars
      = simplCase (arg_vars ++ vars) $ NE.toList $ fmap shift eqns

    shift (EquationInfo (DConP _ _ args :| pats) exp)
      = EquationInfo (to_ne_pats (args ++ pats)) exp
    shift _ = error "Internal error in th-desugar (shift)"

    to_ne_pats :: [DPat] -> NonEmpty DPat
    to_ne_pats pats =
      case pats of
        p:ps -> p:|ps
        [] -> error "Internal error in th-desugar (matchOneCon.to_ne_pats)"

mkDataConCase :: DsMonad q => Name -> NonEmpty CaseAlt -> q MatchResult
mkDataConCase var case_alts = do
  all_ctors <- get_all_ctors (alt_con $ NE.head case_alts)
  return $ \fail ->
    let matches = fmap (mk_alt fail) case_alt_list in
    dCaseE (DVarE var) (matches ++ mk_default all_ctors fail)
  where
    case_alt_list = NE.toList case_alts

    mk_alt fail (CaseAlt con args body_fn)
      = let body = body_fn fail in
        DMatch (DConP con [] (map DVarP args)) body

    mk_default all_ctors fail | exhaustive_case all_ctors = []
                              | otherwise       = [DMatch DWildP fail]

    mentioned_ctors = S.fromList $ map alt_con case_alt_list
    exhaustive_case all_ctors = all_ctors `S.isSubsetOf` mentioned_ctors

    get_all_ctors :: DsMonad q => Name -> q (S.Set Name)
    get_all_ctors con_name = do
      ty_name <- dataConNameToDataName con_name
      Just (DTyConI tycon_dec _) <- dsReify ty_name
      return $ S.fromList $ map get_con_name $ get_cons tycon_dec

    get_cons (DDataD _ _ _ _ _ cons _)     = cons
    get_cons (DDataInstD _ _ _ _ _ cons _) = cons
    get_cons _                             = []

    get_con_name (DCon _ _ n _ _) = n

matchEmpty :: DsMonad q => Name -> q [MatchResult]
matchEmpty var = return [mk_seq]
  where
    mk_seq fail = dCaseE (DVarE var) [DMatch DWildP fail]

matchLiterals :: DsMonad q => NonEmpty Name -> NonEmpty (NonEmpty EquationInfo) -> q MatchResult
matchLiterals (var:|vars) sub_groups
  = do alts <- mapM match_group sub_groups
       return (mkCoPrimCaseMatchResult var alts)
  where
    match_group :: DsMonad q => NonEmpty EquationInfo -> q (Lit, MatchResult)
    match_group eqns
      = do let lit = case firstPat (NE.head eqns) of
                       DLitP lit' -> lit'
                       _          -> error $ "Internal error in th-desugar "
                                          ++ "(matchLiterals.match_group)"
           match_result <- simplCase vars $ NE.toList $ shiftEqns eqns
           return (lit, match_result)

mkCoPrimCaseMatchResult :: Name -- Scrutinee
                        -> NonEmpty (Lit, MatchResult)
                        -> MatchResult
mkCoPrimCaseMatchResult var match_alts = mk_case
  where
    mk_case fail = let alts = NE.toList $ fmap (mk_alt fail) match_alts in
                   dCaseE (DVarE var) (alts ++ [DMatch DWildP fail])
    mk_alt fail (lit, body_fn)
      = DMatch (DLitP lit) (body_fn fail)

matchBangs :: DsMonad q => NonEmpty Name -> NonEmpty EquationInfo -> q MatchResult
matchBangs (var:|vars) eqns
  = do match_result <- simplCase (var:vars) $ NE.toList $
                       fmap (decomposeFirstPat getBangPat) eqns
       return (mkEvalMatchResult var match_result)

decomposeFirstPat :: (DPat -> DPat) -> EquationInfo -> EquationInfo
decomposeFirstPat extractpat (EquationInfo (pat:|pats) body)
  = EquationInfo (extractpat pat :| pats) body

getBangPat :: DPat -> DPat
getBangPat (DBangP p) = p
getBangPat _          = error "Internal error in th-desugar (getBangPat)"

mkEvalMatchResult :: Name -> MatchResult -> MatchResult
mkEvalMatchResult var body_fn fail
  = foldl DAppE (DVarE 'seq) [DVarE var, body_fn fail]

matchVariables :: DsMonad q => NonEmpty Name -> NonEmpty EquationInfo -> q MatchResult
matchVariables (_:|vars) eqns = simplCase vars $ NE.toList $ shiftEqns eqns

shiftEqns :: NonEmpty EquationInfo -> NonEmpty EquationInfo
shiftEqns = fmap shift
  where
    shift (EquationInfo pats rhs) = EquationInfo (to_ne_pats (NE.tail pats)) rhs

    to_ne_pats :: [DPat] -> NonEmpty DPat
    to_ne_pats pats =
      case pats of
        p:ps -> p:|ps
        [] -> error "Internal error in th-desugar (shiftEqns.to_ne_pats)"

adjustMatchResult :: (DExp -> DExp) -> MatchResult -> MatchResult
adjustMatchResult wrap mr fail = wrap $ mr fail

-- from DsUtils
selectMatchVars :: DsMonad q => [DPat] -> q [Name]
selectMatchVars = mapM selectMatchVar

-- from DsUtils
selectMatchVar :: DsMonad q => DPat -> q Name
selectMatchVar (DBangP pat)  = selectMatchVar pat
selectMatchVar (DTildeP pat) = selectMatchVar pat
selectMatchVar (DVarP var)   = newUniqueName ('_' : nameBase var)
selectMatchVar _             = newUniqueName "_pat"
