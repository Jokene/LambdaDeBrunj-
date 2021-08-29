{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}




-------------------------



merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

msort :: Ord a => [a] -> [a]
msort []  = []
msort [x] = [x]
msort xs  = merge (msort (take n xs)) (msort (drop n xs))
  where
    n = div (length xs) 2

-------------------------

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term

instance Show Term where
  show = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

example1 :: Term
example1 = Lambda "a" (Lambda "x" (Apply (Apply (Lambda "y" (Apply (Variable "a") (Variable "c"))) (Variable "x")) (Variable "b")))

numeral :: Int -> Term
numeral i = Lambda "f" (Lambda "x" (numeral' i))
  where
    numeral' i
      | i <= 0    = Variable "x"
      | otherwise = Apply (Variable "f") (numeral' (i-1))

variables :: [String]
variables = map (:[]) ['a'..'z'] ++ [ x : show i | i <- [1..] , x <- ['a'..'z'] ]

free :: Term -> [Var]
free (Variable x) = [x]
free (Lambda x n) = filter (/=x) (free n)
free (Apply  n m) = merge (free n) (free m)





------------------------- Assignment 1


type VarDB = Int
-- consider using newtype for type safety.
data TermDB =
    VariableDB VarDB
  | LambdaDB TermDB
  | ApplyDB TermDB TermDB


instance Show TermDB where
  show = f 0
    where
      f i (VariableDB x) = show x
      f i (LambdaDB m)   = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\." ++ f 0 m
      f i (ApplyDB n m)  = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

example2 :: TermDB
example2 = LambdaDB (ApplyDB (LambdaDB (LambdaDB (ApplyDB (VariableDB 1) (ApplyDB (LambdaDB (VariableDB 0)) (VariableDB 5))))) (ApplyDB (LambdaDB (VariableDB 1)) (VariableDB 1)))

-- maybe this could be optimised? anonymous function perhaps? 
depth :: TermDB -> Int
depth (VariableDB x) = 0
depth (LambdaDB n) = 1 + depth n
depth (ApplyDB n m) = max (depth n) (depth m)



------------------------- Assignment 2


giveNames :: [Var] -> [Var] -> TermDB -> Term
giveNames [] [] _ = error "Empty List was given"
giveNames xs ys (VariableDB i) = Variable (ys!!i) 
giveNames (x:xs) ys (LambdaDB j) = Lambda x (giveNames xs (x:ys) j)
giveNames xs ys (ApplyDB n m) = Apply (giveNames xs ys n) (giveNames xs ys m)


named :: TermDB -> Term
named x = giveNames (take (depth x) variables) (drop (depth x) variables) x



------------------------- Assignment 3


indexOf :: Eq a => a -> [a] -> Int
indexOf j [] = error "EmptyList"
indexOf j xs = head ([y | (x,y) <- zip xs [0..], x == j])


deBruijnList :: [Var] -> Term -> TermDB
deBruijnList xs (Variable x) = VariableDB (indexOf x xs)
deBruijnList xs (Lambda n m) = LambdaDB (deBruijnList (n:xs) m)
deBruijnList xs (Apply n m) = ApplyDB (deBruijnList xs n) (deBruijnList xs m)


deBruijn :: Term -> TermDB
deBruijn x = deBruijnList (free x) x


------------------------- Assignment 4

rift :: Int -> Int -> Int -> TermDB -> TermDB
rift z x y (VariableDB i)
  | x > y  = VariableDB i
  | y == x = VariableDB (i+z)
  | otherwise = VariableDB i

rift z x y (LambdaDB m) = LambdaDB newM
    where
      newM = rift z (x+1) y m

rift z x y (ApplyDB o p) =  ApplyDB newO newP
    where
      newO = rift z x (y+1) o
      newP = rift z x (y+1) p

lift :: Int -> TermDB -> TermDB
lift x = rift x 0 0


sub :: Int -> TermDB -> TermDB -> TermDB
sub z n (VariableDB i)
  | i < z = VariableDB i
  | i == z = lift z n
  | i > z = VariableDB (i-1)

sub z n (LambdaDB x) = LambdaDB newM
          where
            newM = sub (z+1) n x

sub z n (ApplyDB g h) = ApplyDB newG newH
          where
            newG = sub z n g
            newH = sub z n h



reversee :: [a] -> [a]
reversee xs = reverse' xs []

reverse' :: [a] -> [a] -> [a]
reverse' [] ys = ys
reverse' (x:xs) ys = reverse' xs (x : ys)


normal :: TermDB ->  [TermDB]
normal (VariableDB i) = [VariableDB i]
normal (LambdaDB j)  = if length (varthere j) == 1 then newJ else betared ++ newJ  -- consider using case here 
        where
          betared = [sub x (VariableDB x) (LambdaDB j) | x <- varthere j ] -- switch these lines around in the future 
          newJ = normal j
normal (ApplyDB z y) = zGo ++ pGo ++ weGo      --   ++ wGo -- not liking these case statements but i do know how to monad 
        where
          zGo = [ApplyDB a y | a <- normal z]
          pGo = [ApplyDB z b | b <- normal y]
          weGo = case z of
           LambdaDB h -> [ sub x y (LambdaDB h) | x <- varthere h ]
           _               -> []



beta :: TermDB -> [TermDB]
beta (VariableDB y) = [VariableDB y]
beta (LambdaDB z) = [sub x z (VariableDB x) | x <- varthere z]
beta (ApplyDB m n) = [sub v n (VariableDB v) |v <- varthere n ] ++ [sub c m (VariableDB c) |c <- varthere m]

varthere :: TermDB -> [VarDB]
varthere (VariableDB i) = [i]
varthere (LambdaDB x) = varthere x  
varthere (ApplyDB z y) = merge (varthere z) (varthere y)


normalize :: TermDB -> IO ()
normalize term = print (normal term)


-- ------------------------- Assignment 5


isalpha :: Term -> Term -> Bool
isalpha x y
  | null (free x) || null (free y) = False
  | otherwise = free x == free y


