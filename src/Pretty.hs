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

import qualified Data.Text.Lazy                            as TL
import qualified Data.Text.Lazy.IO                         as TL

import           Control.Monad.Reader
import           Data.String
-- import           Prelude hiding ((^^))

import Types

import qualified Unbound.Generics.LocallyNameless as U
import qualified Unbound.Generics.LocallyNameless.Name as U
import qualified Unbound.Generics.LocallyNameless.Bind as U

type PureDoc = P.Doc AnsiStyle

type Doc = PprM PureDoc

type PprE a = PprM a -> PprM a
type PprF a = forall f. Foldable f => f (PprM a) -> PprM a

type DocEndo = PprE PureDoc

type DocFold = PprF PureDoc

renderStdout :: Pretty a => a -> IO ()
renderStdout = renderStdout' id

renderStdout' :: Pretty a => DocEndo -> a -> IO ()
renderStdout' f = TL.putStrLn . renderText' f

putDocW :: Int -> Doc -> IO ()
putDocW w =
  TL.putStrLn
    . TL.replace "\\e" "\ESC"
    . renderLazy
    . P.layoutPretty layoutOpts
    . runPprM
  where layoutOpts = P.LayoutOptions (P.AvailablePerLine w 1.0)

putDoc :: Doc -> IO ()
putDoc = putDocW 100

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

liftDoc :: (Foldable t) => ([a] -> b) -> t (PprM a) -> PprM b
liftDoc f = fmap f . sequence . toList

listed :: DocFold
listed = liftDoc P.list

sep, vsep, hsep, fsep :: DocFold
sep = liftDoc P.sep
vsep = liftDoc P.vsep
hsep = liftDoc P.hsep
fsep = liftDoc P.fillSep

cat, vcat, hcat, fcat :: DocFold
cat = liftDoc P.cat
vcat = liftDoc P.vcat
hcat = liftDoc P.hcat
fcat = liftDoc P.fillCat

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

column :: (Int -> Doc) -> Doc
column f = PprM (\env -> P.column (pprWithEnv env . f))

nesting :: (Int -> Doc) -> Doc
nesting f = PprM (\env -> P.nesting (pprWithEnv env . f))

punctuate :: PureDoc -> [PureDoc] -> [Doc]
punctuate o = fmap pure . P.punctuate o

infixr 5 <+>

(<+>) :: Doc -> Doc -> Doc
(<+>) = liftA2 (P.<+>)

instance Semigroup a => Semigroup (PprM a) where
  (<>) = liftA2 (P.<>)

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

pprPure :: Pretty a => a -> PureDoc
pprPure = runPprM . ppr

applyIf :: Bool -> PprE a -> PprE a
applyIf c f = if c then f else id
{-# INLINE applyIf #-}

above :: Int -> PprE a -> PprE a
above p f m = do
  outerPrec <- view precedence
  applyIf (outerPrec > p) f (assoc (p + 1) m)
{-# INLINE above #-}

nowrap :: PprE a
nowrap = assoc (-1)
{-# INLINE nowrap #-}

parenise :: Int -> Doc -> Doc
parenise prec body = above prec parens body

infixr 8 %%
(%%) = assoc

infixr 8 ^^
(^^) = parenise

class Pretty a where
  ppr :: a -> Doc

instance IsString Doc where fromString = pure . fromString

instance Pretty Bool where ppr = fromString . show
instance Pretty Char where ppr = fromString . show
instance Pretty Int where ppr = fromString . show
instance Pretty Integer where ppr = fromString . show
instance Pretty Double where ppr = fromString . show
instance Pretty Float where ppr = fromString . show

instance Pretty String where ppr = fromString

instance Pretty TL.Text where ppr = fromString . TL.unpack

instance Pretty PrimTy where ppr = pprPrimTy
instance Pretty PrimExp where ppr = pprPrimExp
instance Pretty PrimBinop where ppr = pprPrimBinop
instance Pretty Tm where ppr = pprTm
instance Pretty Co where ppr = pprCo

instance Pretty TmArg where ppr = pprTmArg

instance Pretty (U.Name e) where ppr = pprName

instance Pretty TmAlt where ppr = pprTmAlt

instance Pretty Pat where ppr = pprPat
instance Pretty Konst where ppr = pprKonst

instance Pretty HetEq where ppr = pprHetEq

pprName' :: Bool -> U.Name e -> Doc
pprName' False = \case
  U.Fn s 0 -> ppr s
  U.Fn s n -> ppr s <> ppr n
  -- U.Bn m 0 -> brackets (ppr m)
  -- U.Bn m n -> ppr m <> "@" <> ppr n
pprName' True = \case
  U.Fn s 0 -> annFreeVar (ppr s)
  U.Fn s n -> annFreeVar (ppr s <> ppr n)
  U.Bn m 0 -> annBoundVar ("%" <> ppr m)
  U.Bn m n -> annBoundVar (ppr n <> "%" <> ppr m)

pprName = pprName' True

-- pprNameBind :: Pretty t => U.Bind (U.Name e) t -> Doc
-- pprNameBind (U.B p t) = parens (angles (pprName p) <+> nowrap (ppr t))

bdrPrec = 7
absPrec = 1
annoPrec = 0
appPrec = 11
tightAppPrec = 12
arrPrec = 1
casePrec = 1
letPrec = 1
conPrec = 1

pprApp f x = parenise appPrec (assoc appPrec f <+> x)

pprHetEq :: HetEq -> Doc
pprHetEq (HetEq lt lk rk rt) = ppr lt <+> "~" <+> ppr rt

-- pprBdr :: Bdr -> Doc
-- pprBdr = \case
--   BdrTm (U.B p t) (U.Embed rel) (U.Embed kd) -> parenise
--     bdrPrec
--     (   "λ"
--     <+> varWrap rel (pprName' False p <+> ":" <+> ppr kd)
--     <+> "=>"
--     <+> nowrap (ppr t)
--     )
--   BdrCo heq (U.B p t) -> parenise
--     bdrPrec
--     ( "λ" <+> parens (pprName' False p <+> ":" <+> ppr heq) <+> "=>" <+> nowrap
--       (ppr t)
--     )

varWrap :: Rel -> DocEndo
varWrap = \case
  Rel   -> parens
  Irrel -> braces

annFreeVar :: DocEndo
annFreeVar = annotate (color Yellow)

annBoundVar :: DocEndo
annBoundVar = annotate (color Blue)

annPrimLit :: DocEndo
annPrimLit = annotate (color Red)

primLitSuffix :: Doc
primLitSuffix = ""

primOpSuffix :: Doc
primOpSuffix = ""

pprPrimBinop :: PrimBinop -> Doc
pprPrimBinop = \case
  OpIntAdd -> "+" <> primOpSuffix
  OpIntMul -> "*" <> primOpSuffix

pprPrimTy :: PrimTy -> Doc
pprPrimTy = \case
  TyInt  -> "Int" <> primOpSuffix
  TyBool -> "Bool" <> primOpSuffix
  TyChar -> "Char" <> primOpSuffix

pprPrimExp :: PrimExp -> Doc
pprPrimExp = annPrimLit . \case
  ExpInt  i -> ppr i <> primLitSuffix
  ExpBool b -> ppr b <> primLitSuffix
  ExpChar c -> ppr c <> primLitSuffix

pprTmArg :: TmArg -> Doc
pprTmArg = \case
  TmArgTm tm -> ppr tm
  TmArgCo co -> ppr co

pprTm :: Tm -> Doc
pprTm = \case
  TmPrimTy  p        -> ppr p
  TmPrimExp p        -> ppr p
  TmPrimBinop op l r -> pprBinopApp op l r
  TmVar v            -> ppr v
  TmLam (U.B (BdrTm p (U.Embed rel) (U.Embed kd)) t) -> parenise
    bdrPrec
    (   "λ"
    <+> varWrap rel (pprName' False p <+> ":" <+> ppr kd)
    <+> "=>"
    <+> nowrap (ppr t)
    )
  TmLam (U.B (BdrCo p (U.Embed heq)) t) -> parenise
    bdrPrec
    ( "λ" <+> parens (pprName' False p <+> ":" <+> ppr heq) <+> "=>" <+> nowrap
      (ppr t)
    )
  TmApp f arg       -> pprApp (ppr f) (ppr arg)
  TmCase tm kd alts -> vcat
    [ "case" <+> brackets (ppr kd) <+> ppr tm <+> "of"
    , indent 2 (vcat (map ppr alts))
    ]
  TmConst k  ts -> ppr k <+> braces (hsep (map ppr ts))
  TmCast  tm co -> ppr tm <+> "|>" <+> ppr co

pprTmAlt :: TmAlt -> Doc
pprTmAlt (TmAlt p t) = ppr p <+> "=>" <+> ppr t

pprPat :: Pat -> Doc
pprPat = \case
  PatWild  -> "_"
  PatCon k -> ppr k

pprKonst :: Konst -> Doc
pprKonst = \case
  KType    -> "Type"
  KDtCon c -> ppr c
  KTyCon t -> ppr t

genInfixBin outPrec leftPrec rightPrec mid l r = parenise
  outPrec
  (assoc leftPrec (ppr l) <+> ppr mid <+> assoc rightPrec (ppr r))

leftInfixBin prec = genInfixBin prec prec (prec + 1)
rightInfixBin prec = genInfixBin prec (prec + 1) prec
infixBin prec = genInfixBin prec (prec + 1) (prec + 1)

pprBinopApp :: PrimBinop -> Tm -> Tm -> Doc
pprBinopApp op = case op of
  OpIntAdd -> leftInfixBin 6 op
  OpIntMul -> leftInfixBin 7 op

annCo :: DocEndo
annCo = annotate (color Yellow)

pprCo :: Co -> Doc
pprCo = annCo . \case
  CoRefl t     -> angles (ppr t)
  CoTrans x y  -> ppr x <+> ";" <+> ppr y
  CoLeft  e co -> "left" <+> braces (ppr e) <+> ppr co
  CoRight e co -> "right" <+> braces (ppr e) <+> ppr co
  x            -> ppr (show x)
