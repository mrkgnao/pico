{-# LANGUAGE DeriveAnyClass            #-}
{-# LANGUAGE DeriveDataTypeable        #-}
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

module Types where

import           Edible.Prelude
import           Unbound.Generics.LocallyNameless
import           Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)
import Control.Monad.Trans

data DepQ = MatPi | UnMatPi
  deriving (Show, Generic, Typeable, Alpha, Eq, Subst a)

data Rel = Rel | Irrel
  deriving (Show, Generic, Typeable, Alpha, Eq, Subst a)

-- data Arg =
--   deriving (Show, Generic, Typeable)

-- data Alt
--   deriving (Show, Generic, Typeable)

type TmVar = Name Tm
type CoVar = Name Co

type Kd = Tm
type Ty = Tm

data HetEq = HetEq Ty Kd Kd Ty
  deriving (Show, Generic, Typeable, Alpha, Subst Tm, Subst Co)

data BdrData = CtxTm TmVar Rel Kd | CtxCo CoVar HetEq
  deriving (Show, Generic, Typeable, Alpha)

data Bdr a = BdTm Rel Kd (Bind TmVar a) | BdCo HetEq (Bind CoVar a)
  deriving (Show, Generic, Typeable, Alpha)

data PrimTy = TyInt | TyBool | TyChar
  deriving (Show, Generic, Typeable, Alpha, Subst Co, Subst Tm)

data PrimExp = ExpInt Int | ExpBool Bool | ExpChar Char
  deriving (Show, Generic, Typeable, Alpha, Subst Co, Subst Tm)

data PrimBinop = OpIntAdd | OpIntMul
  deriving (Show, Generic, Typeable, Alpha, Subst Co, Subst Tm)

data Tm
  = TmVar TmVar
  | TmAppTm Tm Tm
  | TmAppCo Tm Co
  | TmPi DepQ (Bdr Tm)
  | TmLam (Bdr Tm)
  | TmCast Tm Co
  | TmFix Tm
  | TmAbsurd Co Tm
  | TmCase Tm Kd [Alt]
  | TmPrimTy PrimTy
  | TmPrimExp PrimExp
  | TmPrimBinop PrimBinop Tm Tm
  | TmConst Konst [Tm]
  deriving (Show, Generic, Typeable, Alpha, Subst Co)

data Alt = Alt { _altPat :: Pat, _altBody :: Tm }
  deriving (Show, Generic, Typeable, Alpha, Subst Tm, Subst Co)

data Pat = PatWild | PatCon Konst
  deriving (Eq, Show, Generic, Typeable, Alpha, Subst Tm, Subst Co)

data Co = CoVar CoVar | CoRefl Tm | CoSym Co | CoTrans Co Co
  deriving (Show, Generic, Typeable, Alpha, Subst Tm)

data Konst = KTyCon String | KDtCon String | KType
  deriving (Eq, Show, Generic, Typeable, Alpha, Subst Tm, Subst Co)

instance Subst Tm Tm where
  isvar (TmVar v) = Just (SubstName v)
  isvar _         = Nothing

instance Subst Co Co where
  isvar (CoVar v) = Just (SubstName v)
  isvar _         = Nothing

instance Subst Tm (Bdr Tm)
instance Subst Tm (Bdr Co)

instance Subst Co (Bdr Co)
instance Subst Co (Bdr Tm)

-- | \\ {r} (v : t) -> b
tlam :: Rel -> TmVar -> Tm -> Tm -> Tm
tlam r v t b = TmLam (BdTm r t (bind v b))

_TmLamCo :: Prism' Tm (HetEq, Bind CoVar Tm)
_TmLamCo = prism (\(h, b) -> TmLam (BdCo h b)) $ \case
  TmLam (BdCo h b) -> Right (h, b)
  x                -> Left x

_TmLamTm :: Rel -> Prism' Tm (Kd, Bind TmVar Tm)
_TmLamTm r = prism (\(k, b) -> TmLam (BdTm r k b)) $ \case
  TmLam (BdTm r' k b) | r == r' -> Right (k, b)
  x                             -> Left x

_TmRelLam :: Prism' Tm (Kd, Bind TmVar Tm)
_TmRelLam = _TmLamTm Rel

_TmIrrelLam :: Prism' Tm (Kd, Bind TmVar Tm)
_TmIrrelLam = _TmLamTm Irrel

type Tele = [BdrData]
data StepEnv = StepEnv { _stepContext :: Tele , _stepRecursionDepth :: Int}

-- makePrisms ''DepQ
-- makePrisms ''Rel
makePrisms ''Tm
makePrisms ''Co
-- makePrisms ''Bdr
makeLenses ''Alt
-- makePrisms ''Pat
makePrisms ''PrimTy
makePrisms ''PrimExp
makePrisms ''PrimBinop

makeLenses ''StepEnv

_TmExpInt :: Prism' Tm Int
_TmExpInt = _TmPrimExp . _ExpInt

tmExpInt :: Int -> Tm
tmExpInt = review _TmExpInt

_TmValue :: Prism' Tm Tm
_TmValue = prism id $ \tm -> if runFreshM (go tm) then Right tm else Left tm
 where
  go :: Tm -> FreshM Bool
  go x = case x of
    -- TODO add H case
    TmPi{}                    -> pure True
    TmLam (BdTm Rel   _ _   ) -> pure True
    TmLam (BdTm Irrel _ body) -> do
      (_, b) <- unbind body
      go b
    TmLam BdCo{} -> pure True
    _            -> pure False

match :: MonadPlus m => Prism' a b -> a -> m b
match p x = maybe mzero pure (x ^? p)

type FreshT = FreshMT
type BaseT m = ReaderT StepEnv (WriterT [String] m)
type BaseM = BaseT Maybe
type StepM = FreshT BaseM

env :: StepEnv
env = StepEnv {_stepContext = [], _stepRecursionDepth = 0}

instance HasRecursionDepth StepEnv where
  recursionDepth = stepRecursionDepth

eval :: Tm -> IO ()
eval = go 0
 where
  go n tm = case step tm of
    Nothing       -> putStrLn (pptm tm)
    Just (tm', l) -> do
      putStrLn ("\nStep #" ++ show n)
      traverse_ putStrLn l
      putStrLn (" ==> " ++ pptm tm')
      go (n + 1) tm'

step :: Tm -> Maybe (Tm, [String])
step tm = stepM tm & runFreshMT & flip runReaderT env & runWriterT

stepM :: Tm -> StepM Tm
stepM tm = asum (stepRules tm)

logT :: String -> StepM ()
logT s = tell [s]

pptm :: Tm -> String
-- pptm tm = "\n" ++ pptm' 0 tm ++ "\n" ++ pptmO tm
pptm = pptm' 0

-- pptmO :: Tm -> String
-- pptmO = \case
--   TmPrimExp (ExpInt x) -> show x
--   TmPrimBinop OpIntAdd x y -> parens (pptmO x) ++ " + " ++ parens (pptmO y)
--   TmPrimBinop OpIntMul x y -> parens (pptmO x) ++ " * " ++ parens (pptmO y)
--   TmAppTm x y -> parens (pptmO x) ++ " " ++ parens (pptmO y)
--   x -> parens (show x)
--   where
--     parens x = "(" ++ x ++ ")"

pptm' :: Int -> Tm -> String
pptm' d = \case
  TmPrimExp (ExpInt x)     -> show x
  TmPrimBinop OpIntAdd x y -> parensIf 6 (pptm' 7 x ++ " + " ++ pptm' 7 y)
  TmPrimBinop OpIntMul x y -> parensIf 7 (pptm' 8 x ++ " * " ++ pptm' 8 y)
  TmAppTm x y              -> parensIf 11 (pptm' 12 x ++ " " ++ pptm' 12 y)
  x                        -> parensIf 11 (show x)
  where parensIf b x = if d > b then "(" ++ x ++ ")" else x

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
  deriving Show

logR :: StepRule -> Tm -> StepM ()
logR s tm = do
  depth <- view recursionDepth
  logT (concat (replicate depth "  ") ++ show s ++ ": " ++ pptm tm)

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
  , s_Match_1
  ]
 where
  stepIntBinop
    :: StepRule -> (Int -> Int -> Int) -> Prism' PrimBinop () -> StepM Tm
  stepIntBinop s f p = do
    logR s tm
    (op, l', r') <- match _TmPrimBinop tm
    match p op
    l <- match (_TmPrimExp . _ExpInt) l'
    r <- match (_TmPrimExp . _ExpInt) r'
    pure (_TmPrimExp # _ExpInt # f l r)

  s_Prim_EvalIntAdd = stepIntBinop S_Prim_EvalIntAdd (+) _OpIntAdd
  s_Prim_EvalIntMul = stepIntBinop S_Prim_EvalIntMul (*) _OpIntMul

  s_BetaRel         = do
    logR S_BetaRel tm
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

  congStep :: StepRule -> Lens' a Tm -> Prism' Tm a -> StepM Tm
  congStep ruleName l pr = review pr <$> do
    logR  ruleName tm
    match pr       tm >>= l stepM

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
    (k, body) <- match _TmIrrelLam tm
    (v, expr) <- unbind body
    s'        <- local (stepContext %~ (|> CtxTm v Irrel k)) (stepM expr)
    pure (_TmIrrelLam # (k, bind v s'))

  s_Binop_Double_Cong = review _TmPrimBinop <$> do
    logR  S_Binop_Double_Cong tm
    match _TmPrimBinop        tm >>= _2 stepM >>= _3 stepM

  s_Binop_Left_Cong  = congStep S_Binop_Left_Cong _2 _TmPrimBinop
  s_Binop_Right_Cong = congStep S_Binop_Right_Cong _3 _TmPrimBinop

  -- Push rules

  s_Trans            = do
    (x, g2) <- match _TmCast tm
    (v, g1) <- match _TmCast x
    pure (_TmCast # (v, _CoTrans # (g1, g2)))

  s_Match_1 = do
    logR S_Match tm
    (scrutinee, _k, alts) <- match _TmCase tm
    (h, phi')             <- match _TmConst scrutinee
    phi                   <- maybe mzero pure (phi' ^? _head)
    let t0 = head (filter (\alt -> alt ^. altPat == PatCon h) alts) ^. altBody
    pure (_TmAppTm # (t0, phi))

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

appTm :: Tm
appTm = TmAppTm idTm (TmVar (s2n "x"))

{-

  case Just 19 of       | case Just 19 of
    Just x  -> 2 + x    |   Just    -> \(x : Int) -> 2 + x
    Nothing -> (-1)     |   Nothing ->               (-1)

-}

caseTm :: Tm
caseTm = TmCase
  (TmConst just [tmExpInt 19])
  (TmPrimTy TyInt)
  [ Alt
    (PatCon just)
    (tlam Rel x (TmPrimTy TyInt) (TmPrimBinop OpIntAdd (tmExpInt 2) (TmVar x)))
  , Alt (PatCon nothing) (tmExpInt (-1))
  ]
 where
  just    = KDtCon "Just"
  nothing = KDtCon "Nothing"

i2 :: Tm
i2 = tmExpInt 2

i3 :: Tm
i3 = tmExpInt 3

i4 :: Tm
i4 = tmExpInt 4

-- arith :: Tm
-- arith = TmAppTm
--   idTm
--   (     (tmExpInt 6 `add` tmExpInt 2 `mul` (tmExpInt 10 `add` tmExpInt 4))
--   `add` (     tmExpInt 9
--         `mul` (tmExpInt 1 `add` tmExpInt 7 `add` tmExpInt 5)
--         )
--   )

--   where
--     infixl 6 `add`
--     add = TmPrimBinop OpIntAdd
--     infixl 7 `mul`
--     mul = TmPrimBinop OpIntMul

-- factTm :: Tm
-- factTm = TmFix (TmLam
