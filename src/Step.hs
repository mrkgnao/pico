{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}

module Step where

import           CustomPrelude
import           Unbound.Generics.LocallyNameless
import           Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)
import           Control.Monad.Trans

import Types
import Pretty

(|+) = (,)

firstWith :: (a -> Bool) -> [a] -> Maybe a
firstWith cond [] = Nothing
firstWith cond (x:xs) | cond x    = Just x
                      | otherwise = firstWith cond xs

withLog :: Applicative m => (r -> m ()) -> (r, m a) -> m a
withLog f (ruleName, rule) = f ruleName *> rule

data PicoEnv = PicoEnv { _tcContext :: Tele, _tcSignature :: Sig, _tcDepth :: Int }
makeLenses ''PicoEnv

env :: PicoEnv
env = PicoEnv {_tcContext = TeleNil, _tcSignature = Sig [], _tcDepth = 0}

instance HasRecursionDepth PicoEnv where recursionDepth = tcDepth

newtype Pico a = Pico { unPico :: FreshMT (ReaderT PicoEnv (WriterT [LogItem Doc] Maybe)) a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadReader PicoEnv
           , MonadWriter [LogItem Doc]
           , MonadPlus
           , Alternative
           , Fresh
           )


withTele :: Tele -> Pico a -> Pico a
withTele ctx = local (tcContext .~ ctx)

withRelevTele :: Tele -> Pico a -> Pico a
withRelevTele = withTele . relev

matchRules :: (RecursionDepthM env m, Alternative m) => [m a] -> m a
matchRules = asum . map recur

matchRulesWith
  :: (RecursionDepthM env m, Alternative m) => (t -> m ()) -> [(t, m a)] -> m a
matchRulesWith f = asum . map (recur . withLog f)

buildJudgment
  :: (RecursionDepthM env m, Alternative m)
  => (s -> t -> m ())
  -> (s -> [(t, m a)])
  -> s
  -> m a
buildJudgment logger rules arg = matchRulesWith (logger arg) (rules arg)

unimplemented = error "unimplemented"

--------------------------------------------------------------------------------
-- Case alternative kinds
--------------------------------------------------------------------------------

altResultKind :: TmAlt -> Kd -> Pico ()
altResultKind alt kd = matchRules (altResultKindRules alt kd)

altResultKindRules :: TmAlt -> Kd -> [Pico ()]
altResultKindRules alt kd = [unimplemented]

--------------------------------------------------------------------------------
-- Type constant kinds, with universals d1 and existentials d2
--------------------------------------------------------------------------------

tyConDecomp :: Tele -> Tele -> Konst -> Pico ()
tyConDecomp d1 d2 h = matchRules (tyConDecompRules d1 d2 h)

tyConDecompRules :: Tele -> Tele -> Konst -> [Pico ()]
tyConDecompRules d1 d2 h = [unimplemented]

--------------------------------------------------------------------------------
-- PropOk
--------------------------------------------------------------------------------

propOk :: HetEq -> Pico ()
propOk h = matchRules (propOkRules h)

propOkRules :: HetEq -> [Pico ()]
propOkRules h = [unimplemented]

--------------------------------------------------------------------------------
-- Type formation
--------------------------------------------------------------------------------

checkTypeKind :: Ty -> Kd -> Pico ()
checkTypeKind ty kd = matchRules (checkTypeKindRules ty kd)

checkTypeKindRules :: Ty -> Kd -> [Pico ()]
checkTypeKindRules ty kd =
  [ do
      kd' <- inferTypeKind ty
      guard (kd `aeq` kd')
  ]

inferTypeKind :: Ty -> Pico Kd
inferTypeKind = buildJudgment logTypeKindRule inferTypeKindRules

data TypeKindRule
  = Ty_Var
  | Ty_Con
  | Ty_AppRel
  | Ty_AppIrrel
  | Ty_CApp
  | Ty_Pi
  | Ty_Cast
  | Ty_Case
  | Ty_Lam
  | Ty_Fix
  | Ty_Absurd
  | Ty_Match
  | Ty_Default
  deriving Show

logTypeKindRule :: Ty -> TypeKindRule -> Pico ()
logTypeKindRule ty s = logText (group (vsep [ppr ty, "-->" <+> ppr (show s)]))

inferTypeKindRules :: Ty -> [(TypeKindRule, Pico Kd)]
inferTypeKindRules ty =
  [ Ty_Var |+ ty_Var
  , Ty_Con |+ ty_Con
  , Ty_AppRel |+ ty_AppRel
  , Ty_AppIrrel |+ ty_AppIrrel
  , Ty_CApp |+ ty_CApp
  , Ty_Pi |+ ty_Pi
  , Ty_Cast |+ ty_Cast
  , Ty_Case |+ ty_Case
  , Ty_Lam |+ ty_Lam
  , Ty_Fix |+ ty_Fix
  , Ty_Absurd |+ ty_Absurd
  , Ty_Match |+ ty_Match
  , Ty_Default |+ ty_Default
  ]

 where
  ty_Var = do
    a      <- match _TmVar ty
    (r, k) <- matchingTmVar a
    match _Rel r
    ctxOk
    pure k
  ty_Con = unimplemented
  ty_AppRel = unimplemented
  ty_AppIrrel = unimplemented
  ty_CApp = unimplemented
  ty_Pi = unimplemented
  ty_Cast = unimplemented
  ty_Case = unimplemented
  ty_Lam = unimplemented
  ty_Fix = unimplemented
  ty_Absurd = unimplemented
  ty_Match = unimplemented
  ty_Default = unimplemented

--------------------------------------------------------------------------------
-- CoSort: coercion formation
--------------------------------------------------------------------------------

-- | Coercion formation
inferCoSort :: Co -> Pico HetEq
inferCoSort = buildJudgment logCoSortRule inferCoSortRules

data CoSortRule
  = Co_Var
  | Co_Sym
  | Co_Trans
  | Co_Refl
  deriving Show

logCoSortRule :: Co -> CoSortRule -> Pico ()
logCoSortRule co s = logText (group (vsep [ppr co, "-->" <+> ppr (show s)]))

findTmVarTele :: MonadPlus m => TmVar -> Tele -> m (Rel, Kd)
findTmVarTele _ TeleNil                              = mzero
findTmVarTele t (TeleBind (unrebind -> (bdr, tele))) = case bdr of
  BdrCo{} -> mzero
  BdrTm t' (Embed r) (Embed k) ->
    if t `aeq` t' then pure (r, k) else findTmVarTele t tele

findCoVarTele :: MonadPlus m => CoVar -> Tele -> m HetEq
findCoVarTele _ TeleNil                              = mzero
findCoVarTele c (TeleBind (unrebind -> (bdr, tele))) = case bdr of
  BdrTm{}            -> mzero
  BdrCo c' (Embed h) -> if c `aeq` c' then pure h else findCoVarTele c tele

matchingCoVar :: CoVar -> Pico HetEq
matchingCoVar c = view tcContext >>= findCoVarTele c

matchingTmVar :: TmVar -> Pico (Rel, Kd)
matchingTmVar c = view tcContext >>= findTmVarTele c

-- TODO separate Pico's reader layer out so that we can pass the
-- environment in just once, instead of to every element of the list
inferCoSortRules :: Co -> [(CoSortRule, Pico HetEq)]
inferCoSortRules co = [Co_Var |+ co_Var, Co_Sym |+ co_Sym, Co_Refl |+ co_Refl]
 where
  co_Var = do
    c <- match _CoVar co
    h <- matchingCoVar c
    ctxOk
    pure h

  co_Sym = do
    g                <- match _CoSym co
    h                <- inferCoSort g
    (t2, k2, k1, t1) <- match _HetEq h
    pure (_HetEq # (t1, k1, k2, t2))

  co_Refl = do
    tm <- match _CoRefl co
    kd <- inferTypeKind tm
    pure (_HetEq # (tm, kd, kd, tm))

--------------------------------------------------------------------------------
-- CtxOk
-- Context well-formedness check.
--------------------------------------------------------------------------------

-- TODO disjointness checks?
ctxOk :: Pico ()
ctxOk = matchRules ctxOkRules

ctxOkRules :: [Pico ()]
ctxOkRules =
  [ do
    t0 <- view tcContext
    match _TeleNil t0
    sigOk
  , do
    t0                        <- view tcContext
    (unrebind -> (bdr, tele)) <- match _TeleBind t0
    -- Ctx_TyVar
    (tv, r, k)                <- match _BdrTm bdr
    withRelevTele tele (checkTypeKind k (TmConst KType []))
    withTele      tele ctxOk
  , do
    t0                        <- view tcContext
    sig                       <- view tcSignature
    (unrebind -> (bdr, tele)) <- match _TeleBind t0
    -- Ctx_CoVar
    (cv, h)                   <- match _BdrCo bdr
    withRelevTele tele (propOk h)
    withTele      tele ctxOk
  -- , throwError "No match"
  ]

--------------------------------------------------------------------------------
-- SigOk
--------------------------------------------------------------------------------

sigOk :: Pico ()
sigOk = matchRules sigOkRules

sigOkRules :: [Pico ()]
sigOkRules =
  [ do
    Sig sig <- view tcSignature
    match _Empty sig
  , do
    Sig sig <- view tcSignature
    (x, xs) <- match _Cons sig
    case x of
      SigTyCon _tc tks -> withTele (teleOfAdtSig tks) ctxOk
      SigDtCon k d t   -> do
        let matchingTyCon = \case
              SigTyCon t' _ -> t == t'
              _             -> False
        SigTyCon _ tks <- liftMaybe (firstWith matchingTyCon sig)
        withTele (teleConcat (teleOfAdtSig tks) d) ctxOk
  ]

teleOfAdtSig :: [(TmVar, Kd)] -> Tele
teleOfAdtSig = \case
  []         -> TeleNil
  (t, k):tks -> TeleBind (rebind (_BdrTm # (t, Irrel, k)) (teleOfAdtSig tks))

teleConcat :: Tele -> Tele -> Tele
teleConcat TeleNil t = t
teleConcat (TeleBind (unrebind -> (bdr, t))) t' =
  TeleBind (rebind bdr (teleConcat t t'))

--------------------------------------------------------------------------------
-- Type-vector formation, forwards
--------------------------------------------------------------------------------

clsVec :: ClsVecArgs -> Pico ()
clsVec = buildJudgment logClsVecRule clsVecRules

data ClsVecArgs = ClsVecArgs [TmArg] Tele

data ClsVecRule
  = Vec_Nil
  | Vec_TyRel
  | Vec_TyIrrel
  | Vec_Co
  deriving Show

logClsVecRule :: ClsVecArgs -> ClsVecRule -> Pico ()
logClsVecRule (ClsVecArgs tas tele) s = logText (group (vsep [ppr (show s)]))

clsVecRules :: ClsVecArgs -> [(ClsVecRule, Pico ())]
clsVecRules args@(ClsVecArgs tas tele) = [Vec_Nil |+ vec_Nil]
 where
  vec_Nil = do
    match _Empty tele
    match _Empty tas
    ctxOk

--------------------------------------------------------------------------------
-- Type-vector formation, reversed
--------------------------------------------------------------------------------

clsCev :: ClsCevArgs -> Pico ()
clsCev = buildJudgment logClsCevRule clsCevRules

data ClsCevArgs = ClsCevArgs [TmArg] Tele

data ClsCevRule
  = Cev_Nil
  | Cev_TyRel
  | Cev_TyIrrel
  | Cev_Co
  deriving Show

logClsCevRule :: ClsCevArgs -> ClsCevRule -> Pico ()
logClsCevRule (ClsCevArgs tas tele) s = logText (group (vsep [ppr (show s)]))

clsCevRules :: ClsCevArgs -> [(ClsCevRule, Pico ())]
clsCevRules args@(ClsCevArgs tas tele) = [Cev_Nil |+ vec_Nil]
 where
  vec_Nil = do
    match _Empty tele
    match _Empty tas
    ctxOk

--------------------------------------------------------------------------------
-- Small-step reduction
--------------------------------------------------------------------------------

type StepArgs = Tm

data StepRule
  = S_BetaRel
  | S_BetaIrrel
  | S_CBeta
  | S_Unroll
  | S_App_Cong_Tm
  | S_App_Cong_Co
  | S_Cast_Cong
  | S_Case_Cong
  | S_Fix_Cong
  | S_IrrelAbs_Cong
  | S_Binop_Left_Cong
  | S_Binop_Right_Cong
  | S_Binop_Double_Cong
  | S_Prim_EvalIntAdd
  | S_Prim_EvalIntMul
  | S_Trans
  | S_Match
  | S_APush
  | S_FPush
  deriving Show

step :: Tm -> Pico Tm
step = buildJudgment logRule stepRules

logRule :: StepArgs -> StepRule -> Pico ()
logRule tm s = logText (group (vsep [ppr tm, "-->" <+> ppr (show s)]))

stepRules :: StepArgs -> [(StepRule, Pico Tm)]
stepRules tm =
  [ S_BetaRel |+ s_BetaRel
  , S_BetaIrrel |+ s_BetaIrrel
  , S_CBeta |+ s_CBeta
  , S_Unroll |+ s_Unroll
  , S_App_Cong_Tm |+ s_App_Cong_Tm
  , S_App_Cong_Co |+ s_App_Cong_Co
  , S_Cast_Cong |+ s_Cast_Cong
  , S_Case_Cong |+ s_Case_Cong
  , S_Fix_Cong |+ s_Fix_Cong
  , S_IrrelAbs_Cong |+ s_IrrelAbs_Cong
  , S_Binop_Double_Cong |+ s_Binop_Double_Cong
  , S_Binop_Right_Cong |+ s_Binop_Right_Cong
  , S_Binop_Left_Cong |+ s_Binop_Left_Cong
  , S_Prim_EvalIntAdd |+ s_Prim_EvalIntAdd
  , S_Prim_EvalIntMul |+ s_Prim_EvalIntMul
  , S_Trans |+ s_Trans
  , S_Match |+ s_Match
  , S_APush |+ s_APush
  , S_FPush |+ s_FPush
  ]
 where
  stepIntBinop :: (Int -> Int -> Int) -> Prism' PrimBinop () -> Pico Tm
  stepIntBinop f p = do
    (op, l', r') <- match _TmPrimBinop tm
    match p op
    l <- match (_TmPrimExp . _ExpInt) l'
    r <- match (_TmPrimExp . _ExpInt) r'
    pure (_TmPrimExp . _ExpInt # f l r)

  s_Prim_EvalIntAdd = stepIntBinop (+) _OpIntAdd
  s_Prim_EvalIntMul = stepIntBinop (*) _OpIntMul

  s_BetaRel         = do
    (f, s2) <- match _TmAppTm tm
    (_, s1) <- match _TmRelLam f
    substInto s1 s2

  -- TODO check value
  s_BetaIrrel = do
    (f, s2) <- match _TmAppTm tm
    (_, s1) <- match _TmIrrelLam f
    substInto s1 s2

  s_CBeta = do
    (f, g) <- match _TmAppCo tm
    (_, s) <- match _TmLamCo f
    substInto s g

  s_Unroll = do
    t         <- match _TmFix tm
    (s, body) <- match _TmRelLam t
    (v, b   ) <- unbind body
    pure (subst v tm b)

  -- Congruence forms

  congStep :: Lens' a Tm -> Prism' Tm a -> Pico Tm
  congStep l pr = review pr <$> do
    match pr tm >>= l step

  cong1 :: Field1 a a Tm Tm => Prism' Tm a -> Pico Tm
  cong1 = congStep _1

  cong :: Prism' Tm Tm -> Pico Tm
  cong            = congStep id

  s_App_Cong_Tm   = cong1 _TmAppTm
  s_App_Cong_Co   = cong1 _TmAppCo
  s_Cast_Cong     = cong1 _TmCast
  s_Case_Cong     = cong1 _TmCase

  s_Fix_Cong      = cong _TmFix

  -- TODO check value
  s_IrrelAbs_Cong = do
    (k, body) <- match _TmIrrelLam tm
    (v, expr) <- unbind body
    s' <- local (tcContext %~ teleSnoc (_BdrTm # (v, Irrel, k))) (step expr)
    pure (_TmIrrelLam # (k, bind v s'))

  s_Binop_Double_Cong = review _TmPrimBinop <$> do
    match _TmPrimBinop tm >>= traverseOf _2 step >>= traverseOf _3 step

  s_Binop_Left_Cong  = congStep _2 _TmPrimBinop
  s_Binop_Right_Cong = congStep _3 _TmPrimBinop

  -- Push rules

  s_Trans            = do
    (x, g2) <- match _TmCast tm
    (v, g1) <- match _TmCast x
    pure (_TmCast # (v, _CoTrans # (g1, g2)))

  s_Match = do
    (scrutinee, _k, tmAlts) <- match _TmCase tm
    (h', phis)              <- match _TmApps scrutinee
    (h , taus)              <- match _TmConst h'

    let matchingTmAlts =
          filter (\tmAlt -> tmAlt ^. tmAltPat == PatCon h) tmAlts
    firstMatch <- match _head matchingTmAlts
    let t0 = firstMatch ^. tmAltBody

    pure (_TmApps # (t0, (_TmArgCo # _CoRefl # h') <| phis))

  -- TODO
  s_APush = do
    (k, bd  ) <- match _TmIrrelLam tm
    (a, body) <- unbind bd
    (v, g   ) <- match _TmCast body
    let t1 = undefined
        t2 = undefined
    let g2 = _CoCoh # (t1, _CoRefl # TmConst KType [], t2)
    undefined

  s_FPush = do
    (lam, g0   ) <- match (_TmFix . _TmCast) tm
    (kd , bdr  ) <- match _TmRelLam lam
    (a  , sigma) <- unbind bdr
    let
      g2 = _CoArgk # g0
      g1 =
        _CoTrans
          # ( _CoApp
              # ( g0
                , _CoArgCo
                . _CoCoh
                # (_TmVar # a, g2, _TmCast # (_TmVar # a, g2))
                )
            , _CoSym # g2
            )

    let fixArg = _TmRelLam # (kd, bind a (_TmCast # (sigma, g1))) -- \(a : k) . (sigma |> g1)

    pure (_TmCast # (_TmFix # fixArg, g2)) -- fix fixArg |> g2

eval :: Tm -> IO ()
eval = go 1
 where
  go :: Int -> Tm -> IO ()
  go n tm = case runStep tm of
    Nothing       -> renderStdout tm
    Just (tm', l) -> do
      putDoc (" #" <> ppr n <+> align (vcat (map applyIndents l)) <> "\n")
      go (n + 1) tm'

applyIndents :: LogItem Doc -> Doc
applyIndents (LogItem n (Msg d)) = indent (2 * n) d

runStep :: Tm -> Maybe (Tm, [LogItem Doc])
runStep tm = step tm & unPico & runFreshMT & flip runReaderT env & runWriterT

substInto
  :: (Fresh m, Typeable b, Alpha c, Subst b c) => Bind (Name b) c -> b -> m c
substInto orig rhs = do
  (v, body) <- unbind orig
  pure (subst v rhs body)

-- | \\ {r} (v : t) -> b
tlam :: Rel -> TmVar -> Tm -> Tm -> Tm
tlam r v t b = TmLam (bind (BdrTm v (Embed r) (Embed t)) b)

-- | \\ {r} (v : t) -> b
tcolam :: CoVar -> HetEq -> Tm -> Tm
tcolam v eq b = TmLam (bind (BdrCo v (Embed eq)) b)

infixl 6 `add`
add = TmPrimBinop OpIntAdd

infixl 7 `mul`
mul = TmPrimBinop OpIntMul

x :: TmVar
x = s2n "x"

y :: TmVar
y = s2n "y"

s :: TmVar
s = s2n "s"

t :: TmVar
t = s2n "t"

idTm :: Tm
idTm = tlam Rel x (TmVar t) (TmVar x)

constTm :: Tm
constTm = tlam Rel x (TmVar s) (tlam Rel y (TmVar t) (TmVar x))

infixr 0 $$
($$) :: Tm -> Tm -> Tm
a $$ b = review _TmAppTm (a, b)

c :: CoVar
c = s2n "c"

{-  case Just 19 of       | case Just_{Int} 19 of
      Just x  -> 2 + x    |   Just    -> \(c : Just_{Int} ~ Just_{Int}) -> 
                                             \(x : Int) -> 
                                              2 + x
-}

appTm :: Tm
appTm = ((constTm $$ (constTm $$ idTm) $$ i2) $$ i3) $$ i4

caseTm :: Tm
caseTm = TmCase
  ( TmApp (TmConst just [TmPrimTy TyInt])
          (TmArgTm (tmExpInt 6 `add` tmExpInt 2))
  )
  -- (TmConst nothing [TmPrimTy TyInt]) 
  (TmPrimTy TyInt)
  [ TmAlt
    (PatCon just)
    ( tcolam
      c
      justEq
      ( tlam Rel
             x
             (TmPrimTy TyInt)
             (tmExpInt 2 `add` TmVar x `mul` (TmVar x `add` tmExpInt (-4)))
      )
    )
  , TmAlt (PatCon nothing) (tcolam c nothingEq (tmExpInt (-1)))
  ]
 where
  nothingEq = HetEq nothing' kmaybe' kmaybe' nothing'
  justEq    = HetEq just' kmaybe' kmaybe' just'
  just      = KDtCon "Just"
  just'     = TmConst just [tyInt]
  nothing   = KDtCon "Nothing"
  nothing'  = TmConst nothing [tyInt]
  kmaybe    = KTyCon "Maybe"
  kmaybe'   = TmConst kmaybe [tyInt]

listNil = KDtCon "ListNil"
tyInt = TmPrimTy TyInt
tyBool = TmPrimTy TyBool
listIsEmpty = TmCase (TmConst listNil [tyInt]) tyBool []

i2 :: Tm
i2 = tmExpInt 2

i3 :: Tm
i3 = tmExpInt 3

i4 :: Tm
i4 = tmExpInt 4

arith :: Tm
arith =
  (tmExpInt 6 `add` tmExpInt 2 `mul` (tmExpInt 10 `add` tmExpInt 4))
    `add` (tmExpInt 9 `mul` (tmExpInt 1 `add` tmExpInt 7 `add` tmExpInt 5))

-- tele :: Tele
-- tele = TeleBind $ rebind (BdrTm x (Embed Rel) (Embed (TmVar x))) $ TeleNil

-- bdr :: Bdr
-- bdr = BdrTm y (Embed Irrel) (Embed (TmVar x))
