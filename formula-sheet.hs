{-# OPTIONS_GHC -Wall #-}

import Data.Char
import Control.Monad
import Control.Applicative
import Data.Maybe
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map

-- parsing helpers (copied from http://dev.stephendiehl.com/fun/002_parsers.html)

newtype Parser a = Parser { parse :: String -> [(a,String)] }

runParser :: Parser a -> String -> a
runParser m s =
  case parse m s of
    [(res, [])] -> res
    [(_, _)]   -> error "Parser did not consume entire stream."
    _           -> error "Parser error."

item :: Parser Char
item = Parser $ \s ->
  case s of
   []     -> []
   (c:cs) -> [(c,cs)]

bind :: Parser a -> (a -> Parser b) -> Parser b
bind p f = Parser $ \s -> concatMap (\(a, s') -> parse (f a) s') $ parse p s

unit :: a -> Parser a
unit a = Parser (\s -> [(a,s)])

instance Functor Parser where
  fmap f (Parser cs) = Parser (\s -> [(f a, b) | (a, b) <- cs s])

instance Applicative Parser where
  pure = return
  (Parser cs1) <*> (Parser cs2) = Parser (\s -> [(f a, s2) | (f, s1) <- cs1 s, (a, s2) <- cs2 s1])

instance Monad Parser where
  return = unit
  (>>=)  = bind

instance MonadPlus Parser where
  mzero = failure
  mplus = combine

instance Alternative Parser where
  empty = mzero
  (<|>) = option

combine :: Parser a -> Parser a -> Parser a
combine p q = Parser (\s -> parse p s ++ parse q s)

failure :: Parser a
failure = Parser (\_ -> [])

option :: Parser a -> Parser a -> Parser a
option  p q = Parser $ \s ->
  case parse p s of
    []     -> parse q s
    res    -> res

satisfy :: (Char -> Bool) -> Parser Char
satisfy p = item `bind` \c ->
  if p c
  then unit c
  else (Parser (\_ -> []))

oneOf :: [Char] -> Parser Char
oneOf s = satisfy (flip elem s)

notOneOf :: [Char] -> Parser Char
notOneOf s = satisfy (not . flip elem s)

chainl :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op a = (p `chainl1` op) <|> return a

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
p `chainl1` op = do {a <- p; rest a}
  where rest a = (do f <- op
                     b <- p
                     rest (f a b))
                 <|> return a

char :: Char -> Parser Char
char c = satisfy (c ==)

natural :: Parser Integer
natural = read <$> some (satisfy isDigit)

string :: String -> Parser String
string [] = return []
string (c:cs) = do { _ <- char c; _ <- string cs; return (c:cs)}

token :: Parser a -> Parser a
token p = do { a <- p; _ <- spaces ; return a}

reserved :: String -> Parser String
reserved s = token (string s)

spaces :: Parser String
spaces = many $ oneOf " \n\r"

digit :: Parser Char
digit = satisfy isDigit

number :: Parser Integer
number = do
  s <- string "-" <|> return []
  cs <- some digit
  return $ read (s ++ cs)

parens :: Parser a -> Parser a
parens m = do
  _ <- reserved "("
  n <- m
  _ <- reserved ")"
  return n

-- exprs and defs

type Var = String

data Expr = Sum Expr Expr
          | Product Expr Expr
          | N Integer
          | Constant String
          | Var Var
          | D Expr Var
          | I Expr Var
          | Expt Expr Expr
          deriving (Show,Eq)

data Def = Def Expr Expr
         deriving (Show,Eq)

minus :: Expr -> Expr
minus x = Product (N (-1)) x

inv :: Expr -> Expr
inv x = Expt x (N (-1))

expandDef :: Def -> [Def]
expandDef (Def l (Sum a b)) = [Def (Sum l (minus a)) b, Def (Sum l (minus b)) a]
expandDef (Def l (Product a b)) = [Def (Product l (inv a)) b, Def (Product l (inv b)) a]
expandDef (Def _ (Var _)) = []
expandDef (Def _ (N _)) = []
expandDef (Def _ (Constant _)) = []
expandDef (Def l (Expt a n)) = [Def (Expt l (inv n)) a]
expandDef (Def l (D y x)) = [Def (I l x) y]
expandDef (Def l (I y x)) = [Def (D l x) y]

fullExpandDef :: Def -> [Def]
fullExpandDef d = (swap d) : (concat $ takeWhile (not . null) $ iterate (concatMap expandDef) $ expandDef d)

swap :: Def -> Def
swap (Def a b) = Def b a

solvesFor :: Var -> Def -> Bool
solvesFor v (Def (Var v') _) = v == v'
solvesFor _ _ = False

solveDefFor :: Var -> Def -> Maybe Def
solveDefFor v d = listToMaybe $ filter (solvesFor v) $ map swap $ fullExpandDef d

-- parser

int :: Parser Expr
int = N <$> number

expr :: Parser Expr
expr = chainl1 term addop

term :: Parser Expr
term = chainl1 factor mulop

factor :: Parser Expr
factor = chainl1 exfactor exptop

exfactor :: Parser Expr
exfactor = parens expr <|> neg expr <|> token atom

neg :: Parser Expr -> Parser Expr
neg f = do
  _ <- reserved "-"
  a <- f
  return $ minus a

var :: Parser Expr
var = do
  h <- satisfy isAlpha
  r <- many (notOneOf " +-*/^()=")
  return $ Var $ h : r

constant :: Parser Expr
constant = Constant <$> (reserved "pi" <|> reserved "epsilon_0") 

atom :: Parser Expr
atom = int <|> constant <|> var

infixOp :: String -> (a -> a -> a) -> Parser (a -> a -> a)
infixOp x f = reserved x >> return f

addop :: Parser (Expr -> Expr -> Expr)
addop = (infixOp "+" Sum) <|> (infixOp "-" (\x y -> Sum x (minus y)))

mulop :: Parser (Expr -> Expr -> Expr)
mulop = (infixOp "*" Product) <|> (infixOp "/" (\x y -> Product x (inv y)))

exptop :: Parser (Expr -> Expr -> Expr)
exptop = infixOp "^" Expt

def :: Parser Def
def = do
  a <- expr
  _ <- reserved "="
  b <- expr
  return $ Def a b

parseDef :: String -> Def
parseDef = runParser def

-- printing

wrapIf :: String -> Bool -> String
wrapIf s True = "(" ++ s ++ ")"
wrapIf s False = s

isSum :: PrintExpr -> Bool
isSum (PSum _) = True
isSum _ = False

isProduct :: PrintExpr -> Bool
isProduct (PProduct _) = True
isProduct _ = False

isExpt :: PrintExpr -> Bool
isExpt (PExpt _ _) = True
isExpt _ = False

toPrintExpr :: Expr -> PrintExpr
toPrintExpr (Sum a b) =
  case a' of
    PSum a'' -> case b' of
      PSum b'' -> PSum $ a'' ++ b''
      _ -> PSum $ a'' ++ [b']
    _ -> case b' of
      PSum b'' -> PSum $ a' : b''
      _ -> PSum [a',b']
  where a' = toPrintExpr a
        b' = toPrintExpr b
toPrintExpr (Product a b) =
  case a' of
    PProduct a'' -> case b' of
      PProduct b'' -> PProduct $ a'' ++ b''
      _ -> PProduct $ a'' ++ [b']
    _ -> case b' of
      PProduct b'' -> PProduct $ a' : b''
      _ -> PProduct [a',b']
  where a' = toPrintExpr a
        b' = toPrintExpr b
toPrintExpr (N i) = PN i
toPrintExpr (Constant c) = PConstant c
toPrintExpr (Var c) = PVar c
toPrintExpr (D y x) = PD (toPrintExpr y) x
toPrintExpr (I y x) = PI (toPrintExpr y) x
toPrintExpr (Expt a b) = PExpt (toPrintExpr a) (toPrintExpr b)

data PrintExpr = PSum [PrintExpr]
               | PProduct [PrintExpr]
               | PN Integer
               | PConstant String
               | PVar Var
               | PD PrintExpr Var
               | PI PrintExpr Var
               | PExpt PrintExpr PrintExpr
               deriving (Show,Eq)

simplifyPExpr :: PrintExpr -> PrintExpr
simplifyPExpr (PExpt x (PN 1)) = x
simplifyPExpr (PProduct [x]) = x
-- recurse :(
simplifyPExpr (PProduct xs) = PProduct $ map simplifyPExpr xs
simplifyPExpr (PSum xs) = PSum $ map simplifyPExpr xs
simplifyPExpr e@(PN _) = e
simplifyPExpr e@(PConstant _) = e
simplifyPExpr e@(PVar _) = e
simplifyPExpr (PD y x) = PD (simplifyPExpr y) x
simplifyPExpr (PI y x) = PI (simplifyPExpr y) x
simplifyPExpr (PExpt a b) = PExpt (simplifyPExpr a) (simplifyPExpr b)

simplifyPExprToFixedPoint :: PrintExpr -> PrintExpr
simplifyPExprToFixedPoint = fixpoint simplifyPExpr

sameExpt :: PrintExpr -> PrintExpr -> Bool
sameExpt (PExpt _ a) (PExpt _ b) = a == b
sameExpt (PExpt _ _) _ = False
sameExpt _ (PExpt _ _) = False
sameExpt _ _ = True

removeExpt :: PrintExpr -> PrintExpr
removeExpt (PExpt x _) = x
removeExpt _ = error "not an PExpt"

hasExpt :: (Integer -> Bool) -> PrintExpr -> Bool
hasExpt f (PExpt _ (PN n)) = f n
hasExpt _ _ = False

apExpt :: (Integer -> Integer) -> PrintExpr -> PrintExpr
apExpt f (PExpt a (PN n)) = PExpt a (PN (f n))
apExpt _ e = e

printProductTerms :: [PrintExpr] -> String
printProductTerms xs = intercalate "*" (map printExpr xs) `wrapIf` (not dontWrap)
  where x' = xs !! 0
        dontWrap = length xs == 1 && not (isSum x' || isProduct x' || isExpt x')

printExptGroup :: [PrintExpr] -> String
printExptGroup xs@((PExpt _ b):_) = printProductTerms (map removeExpt xs) ++ "^" ++ (printExpr b) `wrapIf` (isSum b || isProduct b || isExpt b)        
printExptGroup xs = intercalate "*" $ map printExpr xs

printExpr :: PrintExpr -> String
printExpr (PSum xs) = intercalate "+" $ map printExpr xs
printExpr (PProduct []) = ""
printExpr (PProduct [PN (-1),x]) = "-" ++ (printExpr x) `wrapIf` (isSum x)
printExpr (PProduct [x,PN (-1)]) = "-" ++ (printExpr x) `wrapIf` (isSum x)
printExpr (PProduct xs)
  | null negGroups = intercalate "*" (map printExptGroup posGroups)
  | otherwise = printExpr (PProduct $ concat posGroups) ++ "/" ++ (printExpr x) `wrapIf` (isSum x || isProduct x)
  where exptGroups = groupBy sameExpt xs
        (negGroups,posGroups) = partition (hasExpt (< 0) . head) exptGroups
        x = simplifyPExprToFixedPoint $ PProduct $ concatMap (map (apExpt abs)) negGroups
printExpr (PN n) = show n
printExpr (PConstant c) = c
printExpr (PVar v) = v
printExpr (PD y x) = "d" ++ (printExpr y) `wrapIf` (isSum y) ++ "/d" ++ x
printExpr (PI y x) = "I(" ++ printExpr y ++ ")d" ++ x
printExpr (PExpt a (PN (-1))) = "1/" ++ (printExpr a) `wrapIf` (isSum a || isProduct a)
printExpr (PExpt a b) = (printExpr a) `wrapIf` (isSum a || isProduct a || isExpt a) ++ "^" ++ (printExpr b) `wrapIf` (isSum b || isProduct b || isExpt b)

printDef :: Def -> String
printDef (Def a b) = printExpr (toPrintExpr a) ++ "=" ++ printExpr (toPrintExpr b)

-- simplification (just as needed, very basic)

simplifyExpr :: Expr -> Expr
-- simplify rules
simplifyExpr (Expt (Expt x (N a)) (N b)) = Expt x (N $ a*b)
simplifyExpr (Expt x (N 1)) = x
simplifyExpr e@(Expt (N a) (N b))
  | b > 0 = N $ a ^ b
  | (a == 1 || a == -1) && b == -1 = N a
  | otherwise = e
simplifyExpr (Product (N 1) x) = x
simplifyExpr (Product x (N 1)) = x
simplifyExpr (Expt (Product a b) n@(N _)) = Product (Expt a n) (Expt b n)
simplifyExpr (Product (N a) (N b)) = N $ a * b
-- just recurse
simplifyExpr (Sum a b) = Sum (simplifyExpr a) (simplifyExpr b)
simplifyExpr (Product a b) = Product (simplifyExpr a) (simplifyExpr b)
simplifyExpr (Expt a b) = Expt (simplifyExpr a) (simplifyExpr b)
simplifyExpr (D y x) = D (simplifyExpr y) x
simplifyExpr (I y x) = I (simplifyExpr y) x
simplifyExpr e@(N _) = e
simplifyExpr e@(Var _) = e
simplifyExpr e@(Constant _) = e

fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f x = if x == fx then fx else fixpoint f fx
  where fx = f x

simplifyExprToFixedPoint :: Expr -> Expr
simplifyExprToFixedPoint = fixpoint simplifyExpr

simplifyDef :: Def -> Def
simplifyDef (Def a b) = Def (simplifyExprToFixedPoint a) (simplifyExprToFixedPoint b)

solveDefForAndSimplify :: Var -> Def -> Maybe Def
solveDefForAndSimplify v d = simplifyDef <$> solveDefFor v d

-- formula sheet

data Formula = Formula Def String
  deriving Show

formulasFor :: Var -> [Formula] -> [Formula]
formulasFor v = catMaybes . map (\(Formula d s) -> (\d' -> Formula d' s) <$> solveDefForAndSimplify v d)

printFormula :: Formula -> String
printFormula (Formula d "") = printDef d
printFormula (Formula d ex) = printDef d ++ ", " ++ ex

formula :: DimDefs -> String -> String -> Formula
formula defs d s
  | checkDims defs d' = Formula d' s
  | otherwise = error "bad dims"
  where d' = parseDef d

formulaSheet :: DimDefs -> [(String,String)] -> [Formula]
formulaSheet defs = map (uncurry (formula defs))

physics :: [Formula]
physics = formulaSheet physicsDims
  [ ("F=m*a", "Newton's 2nd law")
  , ("x=x_0+v_0*t+(1/2)*a*t^2", "")
  , ("T=2*pi/omega", "")
  , ("omega=(k_s/m)^(1/2)", "S.H.O.")
  , ("F=(k*q_1*q_2*r_hat)/r^2", "Force between point charges")
  , ("k=1/(4*pi*epsilon_0)", "")
  , ("F=q*E", "Force from electric field")
  , ("E=(k*Q*z*k_hat)/(R_r^2+z^2)^(3/2)", "Field from ring (along center)")
  , ("E=0", "Field inside spherical or cylindrical shell")
  , ("E=(2*k*lambda*r_hat)/r", "Field from infinite line or outside infinite cylinder")
  , ("E=(k*Q*r_hat)/r^2", "Field from point charge")
  , ("E=2*pi*k*sigma*k_hat", "Field from infinite sheet")
  -- , ("J=rho_r*v", "")
  -- , ("v=I/(4*pi*rho_r*r^2)*r_hat", "Velocity field for a point source")
  , ("F=-k_s*x", "Hooke's Law")
  , ("sigma=epsilon_0*E", "Charge density at the surface of a conductor")
  , ("V=EMF", "Ideal battery")
  , ("P=I*V", "Power")
  , ("J=sigma_c*E", "")
  -- , ("v=(q/b)*E", "")
  -- , ("sigma_c=n*q^2/b", "")
  , ("rho_r=1/sigma_c", "Resistivity and conductivity")
  , ("E=rho_r*J", "")
  , ("V=E*L", "")
  , ("R=L/(sigma_c*A)", "")
  , ("R=rho_r*L/A", "")
  , ("P=I^2*R", "Power")
  , ("P=V^2/R", "Power")
  , ("sigma=Q/A", "")
  , ("V=E*d", "")
  , ("Q=C*V", "")
  , ("C=epsilon_0*A/d", "")
  , ("E=E_0/kappa", "Field with dielectric constant")
  , ("C=kappa*epsilon_0*A/d", "Capacitance with dielectric constant")
  , ("U=Q*V/2", "Potential energy")
  , ("U=C*V^2/2", "Potential energy")
  , ("U=Q^2/(2*C)", "Potential energy")
  , ("R_eff=R_1+R_2", "Resistors in series")
  , ("R_eff=1/(1/R_1+1/R_2)", "Resistors in parallel")
  , ("C_eff=1/(1/C_1+1/C_2)", "Capacitors in series")
  , ("C_eff=C_1+C_2", "Capacitors in parallel")
  ]

-- statics :: [Formula]
-- statics = formulaSheet
  -- [ ("tau=T*rho/J", "Torsion")
  -- , ("gamma=tau/G", "")
  -- , ("gamma=phi*rho/L", "")
  -- , ("phi=T*L/(G*J)", "")
  -- , ("phi_1=-r_2/r_1*phi_2", "gears")
  -- , ("T_1=r_1/r_2*T_2", "gears")
  -- ]

printFormulasFor :: [Formula] -> Var -> IO ()
printFormulasFor f = putStr . unlines . map printFormula . (flip formulasFor) f

-- dims

data BaseDim = Time
              | Length
              | Mass
              | Current
              | Temp
              | Amount
              | Luminosity
              deriving (Show,Eq,Ord)

type Dim = [(BaseDim,Integer)]

groupLikeDims :: Dim -> Dim
groupLikeDims xs = map (\g -> (fst (head g),sum (map snd g))) groups
  where groups = groupBy (\a b -> fst a == fst b) xs

normDim :: Dim -> Dim
normDim = filter ((/= 0) . snd) . groupLikeDims . sort

baseFromName :: Char -> BaseDim
baseFromName 'T' = Time
baseFromName 'L' = Length
baseFromName 'M' = Mass
baseFromName 'I' = Current
baseFromName 'O' = Temp
baseFromName 'N' = Amount
baseFromName 'J' = Luminosity
baseFromName _ = error "bad"

baseToName :: BaseDim -> String
baseToName Time = "T"
baseToName Length = "L"
baseToName Mass = "M"
baseToName Current = "I"
baseToName Temp = "O"
baseToName Amount = "N"
baseToName Luminosity = "J"

baseDim :: Parser BaseDim
baseDim = baseFromName <$> oneOf "TLMIONJ"

powerDim :: Parser (BaseDim,Integer)
powerDim = do
  base <- token baseDim
  _ <- reserved "^"
  expt <- number
  return (base,expt)

atomDim :: Parser (BaseDim,Integer)
atomDim = powerDim <|> ((\b -> (b,1)) <$> baseDim)

mulDim :: Integer -> (BaseDim,Integer) -> (BaseDim,Integer)
mulDim x (u,n) = (u,x*n)

divDim :: Integer -> (BaseDim,Integer) -> (BaseDim,Integer)
divDim x (u,n) = (u,n`div`x)

negDim :: (BaseDim,Integer) -> (BaseDim,Integer)
negDim = mulDim (-1)

atomDim' :: Parser Dim
atomDim' = (parens dimChain) <|> (return <$> token atomDim) <|> (reserved "1" >> return [])

dimChain :: Parser Dim
dimChain = chainl1 atomDim' op
  where op = (infixOp "*" (++)) <|> (infixOp "/" (\x y -> x ++ map negDim y))

parseDim :: String -> Dim
parseDim = runParser dimChain

printDim' :: (BaseDim,Integer) -> String
printDim' (u,1) = baseToName u
printDim' (u,n) = baseToName u ++ "^" ++ show n

printDim :: Dim -> String
printDim xs
  | null neg' = posS
  | otherwise = (if null pos then "1" else posS) ++ "/" ++ negS `wrapIf` (length neg' > 1)
  where (pos,neg') = partition ((>0) . snd) xs
        posS = intercalate "*" (map printDim' pos)
        negS = intercalate "*" (map (printDim' . negDim) neg')

makeDim :: String -> Dim
makeDim = normDim . parseDim

type DimDefs = Map Var Dim

physicsDims :: DimDefs
physicsDims = Map.fromList
  [ ("x", makeDim "L")
  , ("x_0", makeDim "L")
  , ("v", makeDim "L/T")
  , ("v_0", makeDim "L/T")
  , ("a", makeDim "L/T^2")
  , ("t", makeDim "T")
  , ("F", makeDim "M*L/T^2")
  , ("m", makeDim "M")
  , ("T", makeDim "T")
  , ("pi", [])
  , ("omega", makeDim "1/T")
  , ("k_s", makeDim "M/T^2")
  , ("k", makeDim "M*L^3*T^-4*I^-2")
  , ("q_1", makeDim "I*T")
  , ("q_2", makeDim "I*T")
  , ("r_hat", [])
  , ("r", makeDim "L")
  , ("epsilon_0", makeDim "1/(M*L^3*T^-4*I^-2)")
  , ("q", makeDim "I*T")
  , ("E", makeDim "L*M*T^-3*I^-1")
  , ("E_0", makeDim "L*M*T^-3*I^-1")
  , ("R", makeDim "M*L^2/(T^3*I^2)")
  , ("R_1", makeDim "M*L^2/(T^3*I^2)")
  , ("R_2", makeDim "M*L^2/(T^3*I^2)")
  , ("R_eff", makeDim "M*L^2/(T^3*I^2)")
  , ("z", makeDim "L")
  , ("k_hat", [])
  , ("Q", makeDim "I*T")
  , ("R_r", makeDim "L")
  , ("lambda", makeDim "I*T/L")
  , ("sigma", makeDim "I*T/L^2")
  , ("J", makeDim "I/L^2")
  , ("rho_r", makeDim "M*L^3*T^-3*I^-2")
  , ("I", makeDim "I")
  , ("V", makeDim "I^-1*L^2*M*T^-3")
  , ("EMF", makeDim "I^-1*L^2*M*T^-3")
  , ("P", makeDim "L^2*M*T^-3")
  , ("sigma_c", makeDim "1/(M*L^3*T^-3*I^-2)")
  , ("L", makeDim "L")
  , ("A", makeDim "L^2")
  , ("d", makeDim "L")
  , ("C", makeDim "I^2*L^-2*M^-1*T^4")
  , ("C_1", makeDim "I^2*L^-2*M^-1*T^4")
  , ("C_2", makeDim "I^2*L^-2*M^-1*T^4")
  , ("C_eff", makeDim "I^2*L^-2*M^-1*T^4")
  , ("kappa", [])
  , ("U", makeDim "L^2*M*T^-2")
  ]

lookupDim :: Var -> DimDefs -> Dim
lookupDim v defs = case Map.lookup v defs of
  Nothing -> error $ v ++ " has no defined dims"
  Just x -> x

evalDim :: DimDefs -> Expr -> Maybe Dim
evalDim defs (Sum a b) = do
  aU <- evalDim defs a
  bU <- evalDim defs b
  guard $ aU == bU
  return aU
evalDim defs (Product a b) = do
  aU <- evalDim defs a
  bU <- evalDim defs b
  return $ normDim $ aU ++ bU
evalDim _ (N _) = Just []
evalDim defs (Constant c) = Just $ lookupDim c defs
evalDim defs (Var v) = Just $ lookupDim v defs
evalDim defs (D y x) = do
  yU <- evalDim defs y
  xU <- return $ lookupDim x defs
  return $ normDim $ yU ++ map negDim xU
evalDim defs (I y x) = do
  yU <- evalDim defs y
  xU <- return $ lookupDim x defs
  return $ normDim $ yU ++ xU
evalDim defs (Expt a (N n)) = do
  aU <- evalDim defs a
  return $ normDim $ map (mulDim n) aU
-- bad and stupid
evalDim defs (Expt a (Product (N n) (Expt (N d) (N (-1))))) = do
  aU <- evalDim defs a
  guard $ all (\u -> mod (snd u) d == 0) aU
  return $ normDim $ map (mulDim n) $ map (divDim d) aU
evalDim _ e = error $ "cannot handle dims: " ++ printExpr (toPrintExpr e)

checkDims :: DimDefs -> Def -> Bool
-- special case (bad)
checkDims _ (Def _ (N 0)) = True -- can just set anything to 0, don't care
checkDims defs (Def a b) = isJust $ do
  aU <- evalDim defs a
  bU <- evalDim defs b
  guard $ aU == bU
  return ()
