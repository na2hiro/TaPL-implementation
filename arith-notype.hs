data Term = Tru
          | Fals
          | If Term Term Term
          | Zero
          | Succ Term
          | Pred Term
          | IsZero Term
          | Var Index
          | Abs Term
          | App Term Term
          deriving Show

type Index = Integer
isJust (Just _) = True
isJust Nothing = False

eval1 :: Term->Maybe Term
eval1 (If Tru t _) = Just t
eval1 (If Fals _ t) = Just t
{-
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
eval1 (App t1 t2) | isJust t1' = t1' >>= \t1'->Just$ App t1' t2
                  | isJust t2' = t2' >>= \t2'->Just$ App t1 t2'
  where t1'=eval1 t1
        t2'=eval1 t2
eval1 (App (Abs x) t2) = Just$ termShift (-1)$ termSubst 0 (termShift 1 t2) x
eval1 _ = Nothing

eval :: Term->Term
eval t = case (eval1 t) of
           Just t2->eval t2
           Nothing->t

termShift :: Index->Term->Term
termShift d t = shift 0 t
  where shift c (Var k) | k<c = Var k
                        | otherwise = Var (k+d)
        shift c (Abs t) = Abs$ shift (c+1) t
        shift c (App t1 t2) = (App (shift c t1) (shift c t2))

termSubst :: Index->Term->Term->Term
termSubst j s (Var k) | k==j = s
                      | otherwise = Var k
termSubst j s (Abs t) = Abs$ termSubst (j+1) (termShift 1 s) t
termSubst j s (App t1 t2) = App (termSubst j s t1) (termSubst j s t2)
