-----------------------------------------------------------------------------
--
-- Module      :  Control.PatternArrows
-- Copyright   :  (c) Phil Freeman 2013
-- License     :  MIT
--
-- Maintainer  :  Phil Freeman <paf31@cantab.net>
-- Stability   :  experimental
-- Portability :
--
-- |
-- Arrows for Pretty Printing
--
-----------------------------------------------------------------------------

{-# LANGUAGE GeneralizedNewtypeDeriving, GADTs, LambdaCase, RankNTypes, TemplateHaskell #-}

module PatArr where

import Data.Char
import Control.Monad.State
import qualified Control.Category as C
import Control.Category ((>>>))
import qualified Control.Arrow as A
import Control.Arrow ((***), (<+>))
import Control.Lens

-- |
-- A first-order runPattern match
--
-- A runPattern is a Kleisli arrow for the @StateT Maybe@ monad. That is, patterns can fail, and can carry user-defined state.
--
newtype Pattern u a b = Pattern { unPattern :: A.Kleisli (StateT u Maybe) a b } deriving (A.Arrow, A.ArrowZero, A.ArrowPlus)

instance C.Category (Pattern u) where
    id = Pattern C.id
    Pattern p1 . Pattern p2 = Pattern (p1 C.. p2)

instance Functor (Pattern u a) where
  fmap f (Pattern p) = Pattern $ A.Kleisli $ fmap f . A.runKleisli p

-- |
-- Run a runPattern with an input and initial user state
--
-- Returns Nothing if the runPattern fails to match
--
runPattern :: Pattern u a b -> u -> a -> Maybe b
runPattern p u = flip evalStateT u . A.runKleisli (unPattern p)

-- |
-- Construct a runPattern from a function
--
mkPattern :: (a -> Maybe b) -> Pattern u a b
mkPattern f = Pattern $ A.Kleisli (lift . f)

patternOf :: Prism' a b -> Pattern u a b
patternOf pr = mkPattern (preview pr)

-- |
-- Construct a runPattern from a stateful function
--
mkPattern' :: (a -> StateT u Maybe b) -> Pattern u a b
mkPattern' = Pattern . A.Kleisli

-- |
-- Construct a runPattern which recursively matches on the left-hand-side
--
chainl :: Pattern u a (a, a) -> (r -> r -> r) -> Pattern u a r -> Pattern u a r
chainl g f p = fix $ \c -> g >>> ((c <+> p) *** p) >>> A.arr (uncurry f)

-- |
-- Construct a runPattern which recursively matches on the right-hand side
--
chainr :: Pattern u a (a, a) -> (r -> r -> r) -> Pattern u a r -> Pattern u a r
chainr g f p = fix $ \c -> g >>> (p *** (c <+> p)) >>> A.arr (uncurry f)

-- |
-- Construct a runPattern which recursively matches on one-side of a tuple
--
wrap :: Pattern u a (s, a) -> (s -> r -> r) -> Pattern u a r -> Pattern u a r
wrap g f p = fix $ \c -> g >>> (C.id *** (c <+> p)) >>> A.arr (uncurry f)

-- |
-- Construct a runPattern which matches a part of a tuple
--
split :: Pattern u a (s, t) -> (s -> t -> r) -> Pattern u a r
split s f = s >>> A.arr (uncurry f)

-- |
-- A table of operators
--
newtype OperatorTable u a r = OperatorTable { runOperatorTable :: [ [Operator u a r] ] }

-- |
-- An operator:
--
--  [@AssocL@] A left-associative operator
--
--  [@AssocR@] A right-associative operator
--
--  [@Wrap@] A prefix-like or postfix-like operator
--
--  [@Split@] A prefix-like or postfix-like operator which does not recurse into its operand
--
data Operator u a r where
  AssocL :: Pattern u a (a, a) -> (r -> r -> r) -> Operator u a r
  AssocR :: Pattern u a (a, a) -> (r -> r -> r) -> Operator u a r
  Wrap   :: Pattern u a (s, a) -> (s -> r -> r) -> Operator u a r
  Split  :: Pattern u a (s, t) -> (s -> t -> r) -> Operator u a r

-- |
-- Build a pretty printer from an operator table and an indecomposable runPattern
--
buildPrettyPrinter :: OperatorTable u a r -> Pattern u a r -> Pattern u a r
buildPrettyPrinter table p = foldl go p (runOperatorTable table)
 where
  go p' ops =
    foldl1
        (<+>)
        ( flip map ops $ \case
          AssocL pat g -> chainl pat g p'
          AssocR pat g -> chainr pat g p'
          Wrap   pat g -> wrap pat g p'
          Split  pat g -> split pat g
        )
      <+> p'

data Eqn = Lit Int
         | Bin Eqn Char Eqn deriving Show

makePrisms ''Eqn

instance Num Eqn where
  fromInteger = Lit . fromIntegral
  a + b = Bin a '+' b
  a * b = Bin a '*' b
  a - b = Bin a '-' b

instance Fractional Eqn where
  a / b = Bin a '/' b

con :: Pattern a Eqn Int
con = patternOf _Lit

bin :: Char -> Pattern a Eqn (Eqn, Eqn)
bin c = mkPattern bin'
 where
  bin' (Bin e1 c' e2) | c == c' = Just (e1, e2)
  bin' _                        = Nothing

eqn :: Pattern a Eqn String
eqn = buildPrettyPrinter ops (fmap show con <+> parenthesize eqn)
 where
  ops = OperatorTable [[binOp '*', binOp '/'], [binOp '+', binOp '-']]
  binOp c = AssocL (bin c) (\e1 e2 -> e1 ++ c : e2)

parenthesize :: Pattern s a String -> Pattern s a String
parenthesize = fmap parens where parens s = '(' : s ++ ")"
