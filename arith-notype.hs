import Prelude hiding (True, False)
data Term = True
          | False
          | If Term Term Term
          | Zero
          | Succ Term
          | Pred Term
          | IsZero Term
          deriving Show

data Value = VTrue
           | VFalse
           | VNum VNum
           deriving Show

data VNum = VZero
          | VSucc VNum
          deriving Show

eval1 :: Term->Term
eval1 (If True t _) = t
eval1 (If False _ t) = t
eval1 (If a b c) = If newa b c
  where newa = eval1 a
eval1 (Succ t) = Succ newt
  where newt = eval1 t
eval1 (Pred Zero) = Zero
eval1 (Pred (Succ n)) = n
eval1 (Pred t) = Pred newt
  where newt = eval1 t
eval1 (IsZero Zero) = True
eval1 (IsZero (Succ n)) = False
eval1 (IsZero t) = IsZero newt
  where newt = eval1 t

eval :: Term->Value
eval True = VTrue
eval False = VFalse
eval Zero = VNum VZero
eval (Succ t) = VNum$ VSucc newt
  where (VNum newt) = eval t
eval t = eval (eval1 t)
