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

import           Control.Lens
import           Control.Monad
import           Data.Foldable
import           Data.Typeable
import           GHC.Generics
import           Unbound.Generics.LocallyNameless
import           Unbound.Generics.LocallyNameless.Internal.Fold (toListOf)
import Control.Monad.Reader

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
makeLenses ''StepEnv
makePrisms ''Alt
makeLenses ''Alt
makePrisms ''Pat

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
match p x = case x ^? p of
  Just y  -> pure y
  Nothing -> mzero

eval :: Tm -> Tm
eval tm = case step tm of
  Nothing  -> tm
  Just tm' -> eval tm'

type FreshT = FreshMT
type StepM = FreshT (ReaderT StepEnv Maybe)

env :: StepEnv
env = StepEnv { _stepContext = [] }

step :: Tm -> Maybe Tm
step tm = runReaderT (stepR tm) env

stepR :: Tm -> ReaderT StepEnv Maybe Tm
stepR tm = runFreshMT (stepM tm)

stepM :: Tm -> StepM Tm
stepM tm = asum (stepRules tm)

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
  , s_Trans
  ]

 where
  s_BetaRel = do
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
    t <- match _TmFix tm
    (s, body) <- match _TmRelLam t
    (v, b) <- unbind body
    pure (subst v tm b)

  -- Congruence forms

  congruenceStep1 :: Prism' Tm Tm -> StepM Tm
  congruenceStep1 pr = match pr tm >>= (review pr <$>) . stepM

  congruenceStep :: Field1 a a Tm Tm => Prism' Tm a -> StepM Tm
  congruenceStep pr = do
    s  <- match pr tm
    s' <- stepM (s ^. _1)
    pure . review pr $ s & _1 .~ s'

  s_App_Cong_Tm = congruenceStep _TmAppTm
  s_App_Cong_Co = congruenceStep _TmAppCo
  s_Cast_Cong   = congruenceStep _TmCast
  s_Case_Cong   = congruenceStep _TmCase

  s_Fix_Cong    = congruenceStep1 _TmFix

  -- TODO check value
  s_IrrelAbs_Cong = do
    (k, body) <- match _TmIrrelLam tm
    (a, s) <- unbind body
    s' <- local (stepContext %~ (|> CtxTm a Irrel k)) (stepM s)
    pure (_TmIrrelLam # (k, bind a s'))
  
  -- Push rules
  
  s_Trans = do
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

