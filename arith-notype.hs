data Term = Tru
          | Fals
          | If Term Term Term
          | Zero
          | Succ Term
          | Pred Term
          | IsZero Term
          | Var Index
          | Abs Type Term
          | App Term Term
          deriving (Show, Eq)

data Type = Bool
          | Nat
          | Arr Type Type
          deriving (Show, Eq)

type Context = [Type]
emptyContext :: Context
emptyContext = []

type Index = Int
isJust (Just _) = True
isJust Nothing = False

eval1 :: Context->Term->Maybe Term
eval1 ctx (If Tru t _) = Just t
eval1 ctx (If Fals _ t) = Just t
{-
eval1 (If t b c) | isJust new = new >>= (\newt->Just$ If newt b c)
  where new = eval1 t
-}
eval1 ctx (If t b c) = eval1 ctx t >>= (\newt->Just$ If newt b c)
eval1 ctx (Succ t) = eval1 ctx t >>= Just. Succ
eval1 ctx (Pred Zero) = Just Zero
eval1 ctx (Pred (Succ n)) = Just n
eval1 ctx (Pred t) = eval1 ctx t >>= Just. Pred
eval1 ctx (IsZero Zero) = Just Tru
eval1 ctx (IsZero (Succ n)) = Just Fals
eval1 ctx (IsZero t) = eval1 ctx t >>= Just. IsZero
eval1 ctx (App t1 t2) | isJust t1' = t1' >>= \t1'->Just$ App t1' t2
                      | isJust t2' = t2' >>= \t2'->Just$ App t1 t2'
  where t1'=eval1 ctx t1
        t2'=eval1 ctx t2
eval1 ctx (App (Abs typ x) t2) = Just$ termShift (-1)$ termSubst 0 (termShift 1 t2) x
eval1 _ _ = Nothing

eval :: Context->Term->Term
eval ctx t = case (eval1 ctx t) of
           Just t2->eval ctx t2
           Nothing->t

termShift :: Index->Term->Term
termShift d t = shift 0 t
  where shift c (Var k) | k<c = Var k
                        | otherwise = Var (k+d)
        shift c (Abs typ t) = Abs typ$ shift (c+1) t
        shift c (App t1 t2) = (App (shift c t1) (shift c t2))

termSubst :: Index->Term->Term->Term
termSubst j s (Var k) | k==j = s
                      | otherwise = Var k
termSubst j s (Abs typ t) = Abs typ$ termSubst (j+1) (termShift 1 s) t
termSubst j s (App t1 t2) = App (termSubst j s t1) (termSubst j s t2)

typeof :: Context->Term->Maybe Type
typeof ctx Tru = Just Bool
typeof ctx Fals = Just Bool
typeof ctx (If t1 t2 t3) | typet1 == Just Bool && typet2 /= Nothing && typet2 == typet3 = typet2
  where typet1 = typeof ctx t1
        typet2 = typeof ctx t2
        typet3 = typeof ctx t3
typeof ctx Zero = Just Nat
typeof ctx (Succ n) | typeof ctx n==Just Nat = Just Nat
typeof ctx (Pred n) | typeof ctx n==Just Nat = Just Nat
typeof ctx (IsZero n) | typeof ctx n==Just Nat = Just Bool
typeof ctx (Var x) = Just (ctx!!x)
typeof ctx (Abs typevar t) | isJust typeterm = typeterm >>= \t->Just$ Arr typevar t
  where typeterm = typeof (typevar:ctx) t
typeof ctx (App t1 t2) | isJust typet1 && isJust typet2 && revealt1 == typet2 = revealt1
  where typet1 = typeof ctx t1
        typet2 = typeof ctx t2
        revealFirst (Just (Arr t _)) = Just t
        revealFirst _ = Nothing
        revealt1 = revealFirst typet1
typeof ctx _ = Nothing
