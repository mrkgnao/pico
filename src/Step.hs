{-# LANGUAGE DeriveAnyClass            #-}
{-# LANGUAGE TupleSections            #-}
{-# LANGUAGE ViewPatterns            #-}
{-# LANGUAGE UndecidableInstances            #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE OverloadedStrings            #-}
{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE TypeSynonymInstances      #-}

module Step where

import           Edible.Prelude
import           Unbound.Generics.LocallyNameless
import           Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)
import           Control.Monad.Trans

import Types
import Pretty

match :: MonadPlus m => Fold a b -> a -> m b
match p x = maybe mzero pure (x ^? p)

-- type SigE env m = (MonadReader env m, HasSig env)
-- class HasSig env where
--   sig :: Lens' env Sig

-- type TeleE env m = (MonadReader env m, HasTele env)
-- class HasTele env where
--   tele :: Lens' env Tele
--

hasKind :: MonadPlus m => Ty -> Kd -> ReaderT (Sig, Tele) m ()
hasKind = undefined

propOk
  :: MonadPlus m
  => HetEq
  -> ReaderT (Sig, Tele) m ()
propOk = undefined

-- | Context well-formedness check.
-- TODO disjointness checks?
ctxOk :: (MonadPlus m, MonadError String m) => Tele -> ReaderT Sig m ()
ctxOk = \case
  TeleNil ->
    -- Ctx_Nil
    sigOk
  TeleBind (unrebind -> (bdr, tele)) -> asum
    [ do
      -- Ctx_TyVar
      (tv, r, k) <- match _BdrTm bdr
      withReaderT (, relevTele tele) (hasKind k (TmConst KType []))
      ctxOk tele
    , do
      -- Ctx_CoVar
      (cv, h) <- match _BdrCo bdr
      withReaderT (, relevTele tele) (propOk h)
      ctxOk tele
    , throwError "No match"
    ]

sigOk :: (MonadPlus m, MonadError String m) => ReaderT Sig m ()
sigOk = do
  s@(Sig sig) <- ask 
  case sig of
    [] ->
      -- Sig_Nil
      pure ()
    (x:xs) -> case x of
                SigTyCon tc tks -> ctxOk (teleOfAdtSig tks)
                SigDtCon k d t  -> do
                  let matchingTyCon = \case
                        SigTyCon t' _ -> t == t'
                        _             -> False
                  SigTyCon _ tks <- liftMaybe (firstWith matchingTyCon sig)
                  ctxOk (teleConcat (teleOfAdtSig tks) d)

firstWith cond [] = Nothing
firstWith cond (x:xs) | cond x    = Just x
                      | otherwise = firstWith cond xs

teleOfAdtSig :: [(TmVar, Kd)] -> Tele
teleOfAdtSig = \case
  []           -> TeleNil
  ((t, k):tks) -> TeleBind (rebind (_BdrTm # (t, Irrel, k)) (teleOfAdtSig tks))

teleConcat :: Tele -> Tele -> Tele
teleConcat TeleNil t = t
teleConcat (TeleBind (unrebind -> (bdr, t))) t' =
  TeleBind (rebind bdr (teleConcat t t'))

liftMaybe :: MonadPlus m => Maybe a -> m a
liftMaybe = maybe mzero pure

type FreshT = FreshMT
type BaseT m = ReaderT StepEnv (WriterT [LogItem Doc] m)
type BaseM = BaseT Maybe
type StepM = FreshT BaseM

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
  go n tm = case step tm of
    Nothing       -> renderStdout tm
    Just (tm', l) -> do
      putDoc (" #" <> ppr n <+> align (vcat (map applyIndents l)) <> "\n")
      go (n + 1) tm'

applyIndents :: LogItem Doc -> Doc
applyIndents (LogItem n (Msg d)) = indent (2 * n) d

step :: Tm -> Maybe (Tm, [LogItem Doc])
step tm = stepM tm & runFreshMT & flip runReaderT env & runWriterT

stepM :: Tm -> StepM Tm
stepM tm = asum (stepRules tm)

logRule :: Tm -> StepRule -> StepM ()
logRule tm s = logText (group (vsep [ppr tm, "-->" <+> ppr (show s)]))

stepRules :: Tm -> [StepM Tm]
stepRules tm = map
  recur
  [ s_BetaRel
  , s_BetaIrrel
  , s_CBeta
  , s_Unroll
  , s_App_Cong_Tm
  , s_App_Cong_Co
  , s_Cast_Cong
  , s_Case_Cong
  , s_Fix_Cong
  , s_IrrelAbs_Cong
  , s_Binop_Double_Cong
  , s_Binop_Right_Cong
  , s_Binop_Left_Cong
  , s_Prim_EvalIntAdd
  , s_Prim_EvalIntMul
  , s_Trans
  , s_Match
  , s_APush
  , s_FPush
  ]
 where
  stepIntBinop
    :: StepRule -> (Int -> Int -> Int) -> Prism' PrimBinop () -> StepM Tm
  stepIntBinop s f p = do
    logRule tm s
    (op, l', r') <- match _TmPrimBinop tm
    match p op
    l <- match (_TmPrimExp . _ExpInt) l'
    r <- match (_TmPrimExp . _ExpInt) r'
    pure (_TmPrimExp . _ExpInt # f l r)

  s_Prim_EvalIntAdd = stepIntBinop S_Prim_EvalIntAdd (+) _OpIntAdd
  s_Prim_EvalIntMul = stepIntBinop S_Prim_EvalIntMul (*) _OpIntMul

  s_BetaRel         = do
    logRule tm S_BetaRel
    (f, s2) <- match _TmAppTm tm
    (_, s1) <- match _TmRelLam f
    substInto s1 s2

  -- TODO check value
  s_BetaIrrel = do
    logRule tm S_BetaIrrel
    (f, s2) <- match _TmAppTm tm
    (_, s1) <- match _TmIrrelLam f
    substInto s1 s2

  s_CBeta = do
    logRule tm S_CBeta
    (f, g) <- match _TmAppCo tm
    (_, s) <- match _TmLamCo f
    substInto s g

  s_Unroll = do
    logRule tm S_Unroll
    t         <- match _TmFix tm
    (s, body) <- match _TmRelLam t
    (v, b   ) <- unbind body
    pure (subst v tm b)

  -- Congruence forms

  congStep :: StepRule -> Lens' a Tm -> Prism' Tm a -> StepM Tm
  congStep ruleName l pr = review pr <$> do
    logRule tm ruleName
    match   pr tm >>= l stepM

  cong1 :: Field1 a a Tm Tm => StepRule -> Prism' Tm a -> StepM Tm
  cong1 s = congStep s _1
  cong :: StepRule -> Prism' Tm Tm -> StepM Tm
  cong s = congStep s id

  s_App_Cong_Tm   = cong1 S_App_Cong_Tm _TmAppTm
  s_App_Cong_Co   = cong1 S_App_Cong_Co _TmAppCo
  s_Cast_Cong     = cong1 S_Cast_Cong _TmCast
  s_Case_Cong     = cong1 S_Case_Cong _TmCase

  s_Fix_Cong      = cong S_Fix_Cong _TmFix

  -- TODO check value
  s_IrrelAbs_Cong = do
    logRule tm S_IrrelAbs_Cong
    (k, body) <- match _TmIrrelLam tm
    (v, expr) <- unbind body
    s' <- local (stepContext %~ teleSnoc (_BdrTm # (v, Irrel, k))) (stepM expr)
    pure (_TmIrrelLam # (k, bind v s'))

  s_Binop_Double_Cong = review _TmPrimBinop <$> do
    logRule tm           S_Binop_Double_Cong
    match   _TmPrimBinop tm >>= _2 stepM >>= _3 stepM

  s_Binop_Left_Cong  = congStep S_Binop_Left_Cong _2 _TmPrimBinop
  s_Binop_Right_Cong = congStep S_Binop_Right_Cong _3 _TmPrimBinop

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
    castedLam    <- match _TmFix tm
    (lam, g0   ) <- match _TmCast castedLam
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

appTm :: Tm
appTm = ((constTm $$ (constTm $$ idTm) $$ i2) $$ i3) $$ i4

-- | \\ {r} (v : t) -> b
tlam :: Rel -> TmVar -> Tm -> Tm -> Tm
tlam r v t b = TmLam (bind (BdrTm v (Embed r) (Embed t)) b)

-- | \\ {r} (v : t) -> b
tcolam :: CoVar -> HetEq -> Tm -> Tm
tcolam v eq b = TmLam (bind (BdrCo v (Embed eq)) b)

c :: CoVar
c = s2n "c"

{-  case Just 19 of       | case Just_{Int} 19 of
      Just x  -> 2 + x    |   Just    -> \(c : Just_{Int} ~ Just_{Int}) -> 
                                             \(x : Int) -> 
                                              2 + x
-}

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

infixl 6 `add`
add = TmPrimBinop OpIntAdd

infixl 7 `mul`
mul = TmPrimBinop OpIntMul

-- tele :: Tele
-- tele = TeleBind $ rebind (BdrTm x (Embed Rel) (Embed (TmVar x))) $ TeleNil

-- bdr :: Bdr
-- bdr = BdrTm y (Embed Irrel) (Embed (TmVar x))
