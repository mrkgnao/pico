{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeSynonymInstances       #-}

module Pretty where

import           Control.Applicative
import           Control.Lens
import           Data.Foldable
import           Data.Semigroup

import           Data.Text.Prettyprint.Doc                 (backslash, dot,
                                                            pipe, pretty)
import qualified Data.Text.Prettyprint.Doc                 as P
import           Data.Text.Prettyprint.Doc.Render.Terminal
import           Data.Text.Prettyprint.Doc.Util            (putDocW)

import qualified Data.Text.Lazy                            as TL
import qualified Data.Text.Lazy.IO                         as TL

import           Control.Monad.Reader
import           Data.String
import           Prelude hiding ((^^))

import Types

type Doc = P.Doc AnsiStyle

type DocM = PprM Doc

type PprE a = PprM a -> PprM a
type PprF a = forall f. Foldable f => f (PprM a) -> PprM a

type DocEndo = PprE Doc

type DocFold = PprF Doc

renderStdout :: Pretty a => a -> IO ()
renderStdout = renderStdout' id

renderStdout' :: Pretty a => DocEndo -> a -> IO ()
renderStdout' f = TL.putStrLn . renderText' f

renderText'' :: Pretty a => Bool -> DocEndo -> a -> TL.Text
renderText'' c f =
  TL.replace "\\e" "\ESC"
    . renderLazy
    . P.layoutPretty layoutOpts
    . runPprM
    . (if c then id else fmap P.unAnnotate)
    . f
    . ppr
  where layoutOpts = P.LayoutOptions (P.AvailablePerLine 110 1.0)

renderText' :: Pretty a => DocEndo -> a -> TL.Text
renderText' = renderText'' True

renderText :: Pretty a => a -> TL.Text
renderText = renderText' id

renderString :: Pretty a => a -> String
renderString = TL.unpack . renderText

renderPlainString :: Pretty a => a -> String
renderPlainString = TL.unpack . renderText'' False id

liftDocM :: (Foldable t) => ([a] -> b) -> t (PprM a) -> PprM b
liftDocM f = fmap f . sequence . toList

listed :: DocFold
listed = liftDocM P.list

sep, vsep, hsep, fsep :: DocFold
sep = liftDocM P.sep
vsep = liftDocM P.vsep
hsep = liftDocM P.hsep
fsep = liftDocM P.fillSep

cat, vcat, hcat, fcat :: DocFold
cat = liftDocM P.cat
vcat = liftDocM P.vcat
hcat = liftDocM P.hcat
fcat = liftDocM P.fillCat

group :: DocEndo
group = fmap P.group

annotate :: AnsiStyle -> DocEndo
annotate = fmap . P.annotate

unAnnotate :: DocEndo
unAnnotate = fmap P.unAnnotate

parens, angles, braces, brackets :: DocEndo
parens = fmap P.parens
angles = fmap P.angles
brackets = fmap P.brackets
braces = fmap P.braces

align :: DocEndo
align = fmap P.align

fill :: Int -> DocEndo
fill = fmap . P.fill

indent :: Int -> DocEndo
indent = fmap . P.indent

nest :: Int -> DocEndo
nest = fmap . P.nest

hang :: Int -> DocEndo
hang = fmap . P.hang

column :: (Int -> PprM Doc) -> PprM Doc
column f = PprM (\env -> P.column (pprWithEnv env . f))

nesting :: (Int -> PprM Doc) -> PprM Doc
nesting f = PprM (\env -> P.nesting (pprWithEnv env . f))

punctuate :: Doc -> [Doc] -> [DocM]
punctuate o = fmap pure . P.punctuate o

infixr 5 <+>

(<+>) :: DocM -> DocM -> DocM
(<+>) = liftA2 (P.<+>)

globalIndentWidth :: Int
globalIndentWidth = 4

newtype PprEnv = PprEnv
  { _pprEnv_precedence :: Int
  }

precedence :: Lens' PprEnv Int
precedence =
  lens _pprEnv_precedence (\e prec -> e { _pprEnv_precedence = prec })

newtype PprM a = PprM
  { unPprM :: PprEnv -> a
  } deriving (Functor, Applicative, Monad, MonadReader PprEnv)

pprWithEnv :: PprEnv -> PprM a -> a
pprWithEnv = flip unPprM

runPprM :: PprM a -> a
runPprM f = unPprM f iEnv where iEnv = PprEnv (-1)

assoc :: Int -> PprE a
assoc p = local (precedence .~ p)

pprPure :: Pretty a => a -> Doc
pprPure = runPprM . ppr

wrapOn :: Bool -> PprE a -> PprE a
wrapOn c f = if c then f else id
{-# INLINE wrapOn #-}

above :: Int -> PprE a -> PprE a
above p f m = do
  outerPrec <- view precedence
  wrapOn (outerPrec > p) f (assoc (p + 1) m)

nowrap :: PprE a
nowrap = assoc (-1)

parenise prec body = above prec parens body

infixr 8 %%
(%%) = assoc

infixr 8 ^^
(^^) = parenise

class Pretty a where
  ppr :: a -> DocM

instance IsString DocM where fromString = pure . fromString

instance Pretty Char where ppr = fromString . show

instance Pretty String where ppr = fromString

instance Pretty TL.Text where ppr = fromString . TL.unpack
