data Term = Tru
          | Fals
          | If Term Term Term
          | Zero
          | Succ Term
          | Pred Term
          | IsZero Term
          | Var Integer
          | Abs Term
          | App Term Term
          deriving Show

eval1 :: Term->Maybe Term
eval1 (If Tru t _) = Just t
eval1 (If Fals _ t) = Just t
{-
isJust (Just _) = True
isJust Nothing = False
eval1 (If t b c) | isJust new = new >>= (\newt->Just$ If newt b c)
  where new = eval1 t
-}
eval1 (If t b c) = eval1 t >>= (\newt->Just$ If newt b c)
eval1 (Succ t) = eval1 t >>= Just. Succ
eval1 (Pred Zero) = Just Zero
eval1 (Pred (Succ n)) = Just n
eval1 (Pred t) = eval1 t >>= Just. Pred
eval1 (IsZero Zero) = Just Tru
eval1 (IsZero (Succ n)) = Just Fals
eval1 (IsZero t) = eval1 t >>= Just. IsZero
eval1 _ = Nothing

eval :: Term->Term
eval t = case (eval1 t) of
           Just t2->eval t2
           Nothing->t
