{-# OPTIONS_GHC -Wall #-}

import Data.Char
import Control.Monad
import Control.Applicative
import Data.Maybe
import Data.List

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

formula :: String -> String -> Formula
formula d s = Formula (parseDef d) s

physics :: [Formula]
physics =
  [ formula "F=m*a" "Newton's 2nd law"
  , formula "x=x_0+v_0*t+(1/2)*a*t^2" ""
  , formula "T=2*pi/omega" ""
  , formula "omega=(k_s/m)^(1/2)" "S.H.O."
  , formula "F=(k*q_1*q_2*r_hat)/r^2" "Force between point charges"
  , formula "k=1/(4*pi*epsilon_0)" ""
  , formula "F=q*E" "Force from electric field"
  , formula "E=(k*Q*z*k_hat)/(R^2+z^2)^(3/2)" "Field from ring (along center)"
  , formula "E=0" "Field inside spherical or cylindrical shell"
  , formula "E=(2*k*lambda*r_hat)/r" "Field from infinite line or outside infinite cylinder"
  , formula "E=(k*Q*r_hat)/r^2" "Field from point charge"
  , formula "E=2*pi*k*sigma*k_hat" "Field from infinite sheet"
  , formula "J=rho_r*v" ""
  , formula "v=I/(4*pi*rho_r*r^2)*r_hat" "Velocity field for a point source"
  , formula "F=-k_s*x" "Hooke's Law"
  , formula "sigma=epsilon_0*E" "Charge density at the surface of a conductor"
  , formula "V=EMF" "Ideal battery"
  , formula "P=I*V" "Power"
  , formula "J=sigma_c*E" ""
  , formula "v=(q/b)*E" ""
  , formula "sigma_c=n*q^2/b" ""
  , formula "rho_r=1/sigma_c" "Resistivity and conductivity"
  , formula "E=rho_r*J" ""
  , formula "V=E*L" ""
  , formula "R=L/(sigma_c*A)" ""
  , formula "R=rho_r*L/A" ""
  , formula "P=I^2*R" "Power"
  , formula "P=V^2/R" "Power"
  , formula "sigma=Q/A" ""
  , formula "V=E*d" ""
  , formula "Q=C*V" ""
  , formula "C=epsilon_0*A/d" ""
  , formula "E=E_0/kappa" "Field with dielectric constant"
  , formula "C=kappa*epsilon_0*A/d" "Capacitance with dielectric constant"
  , formula "U=Q*V/2" "Potential energy"
  , formula "U=C*V^2/2" "Potential energy"
  , formula "U=Q^2/(2*C)" "Potential energy"
  , formula "R_eff=R_1+R_2" "Resistors in series"
  , formula "R_eff=1/(1/R_1+1/R_2)" "Resistors in parallel"
  , formula "C_eff=1/(1/C_1+1/C_2)" "Capacitors in series"
  , formula "C_eff=C_1+C_2" "Capacitors in parallel"
  ]

statics :: [Formula]
statics =
  [ formula "tau=T*rho/J" "Torsion"
  , formula "gamma=tau/G" ""
  , formula "gamma=phi*rho/L" ""
  , formula "phi=T*L/(G*J)" ""
  , formula "phi_1=-r_2/r_1*phi_2" "gears"
  , formula "T_1=r_1/r_2*T_2" "gears"
  ]

printFormulasFor :: [Formula] -> Var -> IO ()
printFormulasFor f = putStr . unlines . map printFormula . (flip formulasFor) f

-- units

data BaseUnit = Time
              | Length
              | Mass
              | Current
              | Temp
              | Amount
              | Luminosity
              deriving (Show,Eq,Ord)

type Unit = [(BaseUnit,Integer)]

groupLikeUnits :: Unit -> Unit
groupLikeUnits xs = map (\g -> (fst (head g),sum (map snd g))) groups
  where groups = groupBy (\a b -> fst a == fst b) xs

normUnit :: Unit -> Unit
normUnit = filter ((/= 0) . snd) . groupLikeUnits . sort

baseFromName :: Char -> BaseUnit
baseFromName 'T' = Time
baseFromName 'L' = Length
baseFromName 'M' = Mass
baseFromName 'I' = Current
baseFromName 'O' = Temp
baseFromName 'N' = Amount
baseFromName 'J' = Luminosity
baseFromName _ = error "bad"

baseToName :: BaseUnit -> String
baseToName Time = "T"
baseToName Length = "L"
baseToName Mass = "M"
baseToName Current = "I"
baseToName Temp = "O"
baseToName Amount = "N"
baseToName Luminosity = "J"

baseUnit :: Parser BaseUnit
baseUnit = baseFromName <$> oneOf "TLMIONJ"

powerUnit :: Parser (BaseUnit,Integer)
powerUnit = do
  base <- token baseUnit
  _ <- reserved "^"
  expt <- number
  return (base,expt)

atomUnit :: Parser (BaseUnit,Integer)
atomUnit = powerUnit <|> ((\b -> (b,1)) <$> baseUnit)

negUnit :: (BaseUnit,Integer) -> (BaseUnit,Integer)
negUnit (u,n) = (u,-n)

pUnit :: Parser Unit
pUnit = chainl1 (return <$> token atomUnit) op
  where op = (infixOp "*" (++)) <|> (infixOp "/" (\x y -> x ++ map negUnit y))

parseUnit :: String -> Unit
parseUnit = runParser pUnit

printUnit' :: (BaseUnit,Integer) -> String
printUnit' (u,1) = baseToName u
printUnit' (u,n) = baseToName u ++ "^" ++ show n

printUnit :: Unit -> String
printUnit xs
  | null neg' = posS
  | otherwise = posS ++ "/" ++ negS `wrapIf` (length neg' > 1)
  where (pos,neg') = partition ((>0) . snd) xs
        posS = intercalate "*" (map printUnit' pos)
        negS = intercalate "*" (map (printUnit' . negUnit) neg')

