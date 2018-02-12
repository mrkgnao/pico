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

data TcEnv = TcEnv { _tcContext :: Tele, _tcSignature :: Sig, _tcDepth :: Int }
makeLenses ''TcEnv

instance HasRecursionDepth TcEnv where recursionDepth = tcDepth

newtype TcM a = TcM { unTcM :: ReaderT TcEnv (WriterT [LogItem Doc] Maybe) a }
  deriving (Functor, Applicative, Monad, MonadReader TcEnv, MonadWriter [LogItem Doc], MonadPlus, Alternative)

withTele :: Tele -> TcM a -> TcM a
withTele ctx = local (tcContext .~ ctx)

withRelevTele :: Tele -> TcM a -> TcM a
withRelevTele = withTele . relev

----------------------------------------------------------------------
-- Stubbed-out judgments
----------------------------------------------------------------------

classifiesVec :: [TmArg] -> Tele -> TcM ()
classifiesVec = undefined

classifiesVecRev :: [TmArg] -> Tele -> TcM ()
classifiesVecRev = undefined

altResultKind :: TmAlt -> Kd -> TcM ()
altResultKind = undefined

-- | Type constant kinds, with universals d1 and existentials d2
tyConDecomp :: Konst -> Tele -> Tele -> Konst -> TcM ()
tyConDecomp h d1 d2 = undefined

-- | Coercion formation
coerSort :: Co -> HetEq -> TcM ()
coerSort co h = asum (coerSortRules co h)

-- | Context well-formedness check.
-- TODO disjointness checks?
ctxOk :: TcM ()
ctxOk = asum ctxOkRules

-- Type formation
typeKind :: Ty -> Kd -> TcM ()
typeKind = undefined

propOk :: HetEq -> TcM ()
propOk = undefined

----------------------------------------------------------------------
  -- CoerSort: coercion formation
----------------------------------------------------------------------

data CoerSortRule
  = Co_Var
  | Co_Sym
  | Co_Trans
  | Co_Refl
  deriving Show

logCoerSortRule :: Co -> HetEq -> CoerSortRule -> TcM ()
logCoerSortRule co h s =
  logText (group (vsep [ppr co, ":", ppr h, "-->" <+> ppr (show s)]))

-- TODO separate TcM's reader layer out so that we can pass the
-- environment in just once, instead of to every element of the list
coerSortRules :: Co -> HetEq -> [TcM ()]
coerSortRules co h =
  [ do
      logCoerSortRule co h Co_Sym
      g                <- match _CoSym co
      (t2, k2, k1, t1) <- match _HetEq h
      coerSort g (_HetEq # (t1, k1, k2, t2))
  , do
      logCoerSortRule co h Co_Refl
      tm <- match _CoRefl co
      (t1, k1, k1', t1') <- match _HetEq h
      -- assert (k1 == k1')
      typeKind tm k1
  ]

----------------------------------------------------------------------
  -- CtxOk
----------------------------------------------------------------------

ctxOkRules :: [TcM ()]
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
    withRelevTele tele (typeKind k (TmConst KType []))
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

----------------------------------------------------------------------
  -- SigOk
----------------------------------------------------------------------

sigOk :: TcM ()
sigOk = view tcSignature >>= \s@(Sig sig) -> case sig of
  [] ->
    -- Sig_Nil
    pure ()
  (x:xs) -> case x of
    SigTyCon tc tks -> withTele (teleOfAdtSig tks) ctxOk
    SigDtCon k d t  -> do
      let matchingTyCon = \case
            SigTyCon t' _ -> t == t'
            _             -> False
      SigTyCon _ tks <- liftMaybe (firstWith matchingTyCon sig)
      withTele (teleConcat (teleOfAdtSig tks) d) ctxOk

firstWith :: (a -> Bool) -> [a] -> Maybe a
firstWith cond [] = Nothing
firstWith cond (x:xs) | cond x    = Just x
                      | otherwise = firstWith cond xs

teleOfAdtSig :: [(TmVar, Kd)] -> Tele
teleOfAdtSig = \case
  []         -> TeleNil
  (t, k):tks -> TeleBind (rebind (_BdrTm # (t, Irrel, k)) (teleOfAdtSig tks))

teleConcat :: Tele -> Tele -> Tele
teleConcat TeleNil t = t
teleConcat (TeleBind (unrebind -> (bdr, t))) t' =
  TeleBind (rebind bdr (teleConcat t t'))

----------------------------------------------------------------------
  -- Small-step reduction
----------------------------------------------------------------------

type FreshT = FreshMT
type BaseT m = ReaderT StepEnv (WriterT [LogItem Doc] m)
type StepM = FreshT (BaseT Maybe)

data StepEnv = StepEnv { _stepContext :: Tele , _stepRecursionDepth :: Int}
makeLenses ''StepEnv

env :: StepEnv
env = StepEnv {_stepContext = TeleNil, _stepRecursionDepth = 0}

instance HasRecursionDepth StepEnv where
  recursionDepth = stepRecursionDepth

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
runStep tm = step tm & runFreshMT & flip runReaderT env & runWriterT

step :: Tm -> StepM Tm
step tm = asum (stepRules tm)

logRule :: Tm -> StepRule -> StepM ()
logRule tm s = logText (group (vsep [ppr tm, "-->" <+> ppr (show s)]))

stepRules :: Tm -> [StepM Tm]
stepRules tm = map
  (\(rule, f) -> recur (logRule tm rule *> f))
  [ (S_BetaRel          , s_BetaRel)
  , (S_BetaIrrel        , s_BetaIrrel)
  , (S_CBeta            , s_CBeta)
  , (S_Unroll           , s_Unroll)
  , (S_App_Cong_Tm      , s_App_Cong_Tm)
  , (S_App_Cong_Co      , s_App_Cong_Co)
  , (S_Cast_Cong        , s_Cast_Cong)
  , (S_Case_Cong        , s_Case_Cong)
  , (S_Fix_Cong         , s_Fix_Cong)
  , (S_IrrelAbs_Cong    , s_IrrelAbs_Cong)
  , (S_Binop_Double_Cong, s_Binop_Double_Cong)
  , (S_Binop_Right_Cong , s_Binop_Right_Cong)
  , (S_Binop_Left_Cong  , s_Binop_Left_Cong)
  , (S_Prim_EvalIntAdd  , s_Prim_EvalIntAdd)
  , (S_Prim_EvalIntMul  , s_Prim_EvalIntMul)
  , (S_Trans            , s_Trans)
  , (S_Match            , s_Match)
  , (S_APush            , s_APush)
  , (S_FPush            , s_FPush)
  ]
 where
  stepIntBinop :: (Int -> Int -> Int) -> Prism' PrimBinop () -> StepM Tm
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

  congStep :: Lens' a Tm -> Prism' Tm a -> StepM Tm
  congStep l pr = review pr <$> do
    match pr tm >>= l step

  cong1 :: Field1 a a Tm Tm => Prism' Tm a -> StepM Tm
  cong1 = congStep _1

  cong :: Prism' Tm Tm -> StepM Tm
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
    s' <- local (stepContext %~ teleSnoc (_BdrTm # (v, Irrel, k))) (step expr)
    pure (_TmIrrelLam # (k, bind v s'))

  s_Binop_Double_Cong = review _TmPrimBinop <$> do
    match _TmPrimBinop tm >>= _2 step >>= _3 step

  s_Binop_Left_Cong  = congStep _2 _TmPrimBinop
  s_Binop_Right_Cong = congStep _3 _TmPrimBinop

  -- Push rules

  s_Trans            = do
    logRule tm S_Trans
    (x, g2) <- match _TmCast tm
    (v, g1) <- match _TmCast x
    pure (_TmCast # (v, _CoTrans # (g1, g2)))

  s_Match = do
    logRule tm S_Match
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
    logRule tm S_APush
    (k, bd  ) <- match _TmIrrelLam tm
    (a, body) <- unbind bd
    (v, g   ) <- match _TmCast body
    let t1 = undefined
        t2 = undefined
    let g2 = _CoCoh # (t1, _CoRefl # TmConst KType [], t2)
    undefined

  s_FPush = do
    logRule tm S_FPush
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
