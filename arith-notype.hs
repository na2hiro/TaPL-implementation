import Control.Monad.Error
import Control.Monad

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
          | VUnit
          | As Term Type
          | Let Term Term
          deriving (Show, Eq)

data Type = Bool
          | Nat
          | Arr Type Type
          | Unit
          deriving (Show, Eq)

data MyError = TypeMismatch TypeName Type
             | Default String

type TypeName = String

instance Error MyError where
    noMsg = Default "An error has occurred"
    strMsg = Default

showError :: MyError -> String
showError (Default str) = str
showError (TypeMismatch expected found) = "Invalid type: expected "++ expected ++ ", found "++show found

instance Show MyError where show = showError

type Context = [Type]
type ThrowsError = Either MyError
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
eval1 ctx (App (Abs typ x) t2) = Just$ termSubstTop t2 x
eval1 ctx (As t ty) =case eval1 ctx t of
                       Just t'->return$ As t' ty
                       Nothing->return t
eval1 ctx (Let t1 t2) = case eval1 ctx t1 of
                          Just t'->return$ Let t' t2
                          Nothing->return$ termSubstTop t1 t2
eval1 _ _ = Nothing

eval :: Context->Term->Term
eval ctx t = case (eval1 ctx t) of
           Just t2->eval ctx t2
           Nothing->t

--ドブラウンシフト
termShift :: Index->Term->Term
termShift d t = shift 0 t
  where shift c (Var k) | k<c = Var k
                        | otherwise = Var (k+d)
        shift c (Abs typ t) = Abs typ$ shift (c+1) t
        shift c (App t1 t2) = (App (shift c t1) (shift c t2))
        shift c (If t1 t2 t3) = (If (shift c t1) (shift c t2) (shift c t3))
        shift c t = t

--代入
termSubst :: Index->Term->Term->Term
termSubst j s (Var k) | k==j = s
                      | otherwise = Var k
termSubst j s (Abs typ t) = Abs typ$ termSubst (j+1) (termShift 1 s) t
termSubst j s (App t1 t2) = App (termSubst j s t1) (termSubst j s t2)
termSubst j s (If t1 t2 t3) = If (termSubst j s t1) (termSubst j s t2) (termSubst j s t3)
termSubst j s t = t

termSubstTop s t = termShift(-1)(termSubst 0 (termShift 1 s) t)


typeof :: Context->Term->ThrowsError Type
typeof ctx Tru = return Bool
typeof ctx Fals = return Bool
typeof ctx (If t1 t2 t3) = do
    typet1 <- typeof ctx t1
    typet2 <- typeof ctx t2
    typet3 <- typeof ctx t3
    case typet1 == Bool of
      False->throwError$ TypeMismatch (show Bool) typet1
      True->case typet2 == typet3 of
        False->throwError$ TypeMismatch (show typet2) typet3
        True->return typet2
typeof ctx Zero = return Nat
typeof ctx (Succ n) = do
    typet <-typeof ctx n
    if typet==Nat then return Nat else throwError$ TypeMismatch (show Nat) typet
typeof ctx (Pred n) = do
    typet <- typeof ctx n
    if typet==Nat then return Nat else throwError$ TypeMismatch (show Nat) typet
typeof ctx (IsZero n) = do
    typet <- typeof ctx n
    if typet==Nat then return Bool else throwError$ TypeMismatch (show Nat) typet
typeof ctx (Var x) = return (ctx!!x)
typeof ctx (Abs typevar t) = do
    typet <- typeof (typevar:ctx) t
    return$ Arr typevar typet
typeof ctx (App t1 t2) = do
    typet1 <- typeof ctx t1
    typet2 <- typeof ctx t2
    revealt1 <- revealFirst typet1
    if revealt1 == typet2 then return revealt1 else throwError$ TypeMismatch (show typet2) revealt1
  where 
        revealFirst (Arr t _) = return t
        revealFirst t = throwError$ TypeMismatch "Arrow type" t
typeof ctx VUnit = return Unit
typeof ctx (As t ty) = do
    tty <- typeof ctx t
    if tty==ty then return ty else throwError$ TypeMismatch (show ty) tty
typeof ctx (Let t1 t2) = do
    typet1 <- typeof ctx t1
    typet2 <- typeof (typet1:ctx) t2
    return typet2
typeof ctx _ = throwError$ Default "no pattern matched"
