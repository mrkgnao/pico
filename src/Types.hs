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

data BdrData = CtxTm TmVar !Rel !Kd | CtxCo CoVar !HetEq
  deriving (Show, Generic, Typeable, Alpha)

data Bdr a = BdTm !Rel !Kd (Bind TmVar a) | BdCo !HetEq (Bind CoVar a)
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
  | TmPi !DepQ (Bdr Tm)
  | TmLam (Bdr Tm)
  | TmCast Tm Co
  | TmFix Tm
  | TmAbsurd Co Tm
  | TmCase Ty Kd [Alt]
  | TmPrimTy PrimTy
  | TmPrimExp PrimExp
  | TmPrimBinop PrimBinop Tm Tm
  deriving (Show, Generic, Typeable, Alpha, Subst Co)

data Alt = Alt { _altPat :: !Pat, _altType :: !Ty }
  deriving (Show, Generic, Typeable, Alpha, Subst Tm, Subst Co)

data Pat = PatWild | PatCon
  deriving (Show, Generic, Typeable, Alpha, Subst Tm, Subst Co)

data Co = CoVar CoVar | CoRefl Tm | CoSym Co | CoTrans Co Co
  deriving (Show, Generic, Typeable, Alpha, Subst Tm)

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
data StepEnv = StepEnv { _stepContext :: Tele }

makePrisms ''DepQ
makePrisms ''Rel
makePrisms ''Tm
makePrisms ''Co
makePrisms ''Bdr
makePrisms ''Alt
makePrisms ''Pat
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
type BaseM = ReaderT StepEnv (WriterT [String] Maybe)
type StepM = FreshT BaseM

env :: StepEnv
env = StepEnv {_stepContext = []}

eval :: Tm -> IO ()
eval tm = case step tm of
  Nothing       -> print tm
  Just (tm', l) -> do
    traverse_ putStrLn l
    eval tm'

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
  TmPrimExp (ExpInt x) -> show x
  TmPrimBinop OpIntAdd x y -> parensIf 6 (pptm' 7 x ++ " + " ++ pptm' 7 y)
  TmPrimBinop OpIntMul x y -> parensIf 7 (pptm' 8 x ++ " * " ++ pptm' 8 y)
  TmAppTm x y -> parensIf 11 (pptm' 12 x ++ " " ++ pptm' 12 y)
  x -> parensIf 11 (show x)
  where 
    parensIf b x = if d > b then "(" ++ x ++ ")" else x

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
  | S_Prim_EvalIntAdd
  | S_Prim_EvalIntMul
  | S_Trans
  deriving Show

logR :: StepRule -> Tm -> StepM ()
logR s tm = logT (show s ++ ": " ++ pptm tm)

stepRules :: Tm -> [StepM Tm]
stepRules tm =
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
  , s_Binop_Left_Cong
  , s_Binop_Right_Cong
  , s_Prim_EvalIntAdd
  , s_Prim_EvalIntMul
  , s_Trans
  ]
 where
  stepIntBinop
    :: StepRule -> (Int -> Int -> Int) -> Prism' PrimBinop () -> StepM Tm
  stepIntBinop s f p = do
    (op, l', r') <- match _TmPrimBinop tm
    match p op
    l <- match (_TmPrimExp . _ExpInt) l'
    r <- match (_TmPrimExp . _ExpInt) r'
    logR s tm
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

  congStep :: Lens' a Tm -> Prism' Tm a -> StepRule -> StepM Tm
  congStep getTm pr s = review pr <$> do
    tm' <- match pr tm
    logR s tm
    getTm stepM tm'

  cong1 :: Field1 a a Tm Tm => Prism' Tm a -> StepRule -> StepM Tm
  cong1 = congStep _1

  cong :: Prism' Tm Tm -> StepRule -> StepM Tm
  cong            = congStep id

  s_App_Cong_Tm   = cong1 _TmAppTm S_App_Cong_Tm
  s_App_Cong_Co   = cong1 _TmAppCo S_App_Cong_Co
  s_Cast_Cong     = cong1 _TmCast S_Cast_Cong
  s_Case_Cong     = cong1 _TmCase S_Case_Cong

  s_Fix_Cong      = cong _TmFix S_Fix_Cong

  -- TODO check value
  s_IrrelAbs_Cong = do
    (k, body) <- match _TmIrrelLam tm
    (a, s   ) <- unbind body
    s'        <- local (stepContext %~ (|> CtxTm a Irrel k)) (stepM s)
    pure (_TmIrrelLam # (k, bind a s'))

  s_Binop_Left_Cong  = congStep _2 _TmPrimBinop S_Binop_Left_Cong
  s_Binop_Right_Cong = congStep _3 _TmPrimBinop S_Binop_Right_Cong

  -- Push rules

  s_Trans            = do
    (x, g2) <- match _TmCast tm
    (v, g1) <- match _TmCast x
    pure (_TmCast # (v, _CoTrans # (g1, g2)))

substInto
  :: (Fresh m, Typeable b, Alpha c, Subst b c) => Bind (Name b) c -> b -> m c
substInto orig rhs = do
  (v, body) <- unbind orig
  pure (subst v rhs body)

x :: TmVar
x = s2n "x"

t :: TmVar
t = s2n "t"

idTm :: Tm
idTm = tlam Rel x (TmVar t) (TmVar x)

appTm :: Tm
appTm = TmAppTm idTm (TmVar (s2n "x"))

six :: Tm
six = TmAppTm
  idTm
  ( TmPrimBinop
    OpIntAdd
    ( TmPrimBinop
      OpIntMul
      ( TmPrimBinop OpIntAdd
                    (tmExpInt 2)
                    (TmPrimBinop OpIntMul (tmExpInt 6) (tmExpInt 2))
      )
      (tmExpInt 10)
    )
    (TmPrimBinop OpIntMul (tmExpInt 6) (tmExpInt 2))
  )

-- factTm :: Tm
-- factTm = TmFix (TmLam
