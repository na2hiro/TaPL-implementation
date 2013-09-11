import Control.Monad.Error
import Data.List(intercalate)
import Data.Map
import Data.Traversable as T
import Data.Monoid
import Data.Foldable(foldMap)

main=putStrLn "hello"

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
          | Unit
          | As Term Type
          | Let Term Term
          | Rec (Map FieldName Term)
          | Vari Label Term
          | Case Term (Map Label Term)
          | Proj Term FieldName
          | Fold Type Term
          | Unfold Type Term
          deriving (Eq)

data Type = Bool
          | Nat
          | Arr Type Type
          | TUnit
          | Record (Map FieldName Type)
          | Variant (Map Label Type)
          | Top
          | TVar TypeVarName
          | Mu TypeVarName Type
          deriving (Eq)

data MyError = TypeMismatch TypeName Type
             | FieldNotFound FieldName
             | LabelNotFound Label
             | Default String

type TypeName = String
type FieldName = String
type TypeVarName = String
type Label = String

instance Error MyError where
    noMsg = Default "An error has occurred"
    strMsg = Default

showError :: MyError -> String
showError (Default str) = str
showError (TypeMismatch expected found) = "Invalid type: expected "++ expected ++ ", found "++show found
showError (FieldNotFound field) = "Field "++field++" not found on record"
showError (LabelNotFound field) = "Label "++field++" not found on variant"

showTerm :: Term -> String
showTerm Tru = "true"
showTerm Fals = "false"
showTerm (If a b c) = "if "++show a++" then "++show b++" else "++show c
showTerm Zero = "zero"
showTerm (Succ t) = "succ "++show t
showTerm (Pred t) = "pred "++show t
showTerm (IsZero t) = "iszero "++show t
showTerm (Var i) = show i
showTerm (Abs typ term) = "(\\:"++show typ++"."++show term++")"
showTerm (App t1 t2) = "("++show t1++" "++show t2++")"
showTerm Unit = "unit"
showTerm (As term typ) = show term++" as "++show typ
showTerm (Let t1 t2) = "let "++show t1++" in "++show t2
showTerm (Rec mp) = "{"++intercalate "," (Prelude.map (\(k,v)->k++"="++show v)$ toList mp)++"}"
showTerm (Proj t name) = show t++"."++name
showTerm (Vari label term) = "<"++label++"="++show term++">"
showTerm (Case term mp) = "case "++showTerm term++" of "++(intercalate " | "$ Prelude.map (\(label,t)->label++"=>"++show t)$ toList mp)
showTerm (Fold typ term) = "fold ["++show typ++"] "++show term
showTerm (Unfold typ term) = "unfold ["++show typ++"] "++show term

instance Show Term where show = showTerm

showType :: Type->String
showType Bool = "Bool"
showType Nat = "Nat"
showType (Arr t1 t2) = "("++show t1++" -> "++show t2++")"
showType TUnit = "Unit"
showType (Record mp) = "{"++intercalate "," (Prelude.map (\(k,v)->k++":"++show v)$ toList mp)++"}"
showType (Variant mp) = "<"++intercalate "," (Prelude.map (\(k,v)->k++":"++show v)$ toList mp)++">"
showType Top = "Top"
showType (TVar name) = name
showType (Mu name typ) = "Mu "++name++"."++show typ

instance Show Type where show = showType

instance Show MyError where show = showError

type Context = [Type]
type ThrowsError = Either MyError
emptyContext :: Context
emptyContext = []

type Index = Int
isJust (Just _) = True
isJust Nothing = False

replaceTVar::TypeName->Type->Type->Type
replaceTVar ty x (Arr t1 t2) = Arr (replaceTVar ty x t1) (replaceTVar ty x t2)
replaceTVar ty x (Record mp) = Record$ fmap (replaceTVar ty x) mp
replaceTVar ty x (TVar ty2) | ty==ty2 = x
replaceTVar _ _ t = t

replace::Type->Type->Type->Type
replace from to val | val==from = to
replace from to (Arr t1 t2) = Arr (replace from to t1) (replace from to t2)
replace from to (Record mp) = Record$ fmap (replace from to) mp
replace (TVar varname) to mu@(Mu varname2 body) | varname==varname2 = mu
replace from to (Mu varname body) = Mu varname (replace from to body)
replace _ _ body = body 

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
eval1 ctx (As t ty) = case t of
                        Vari label term -> eval1 ctx term >>= (\term'->return$As (Vari label term') ty)
                        otherwise -> maybe (return t) (\t'->return$ As t' ty)$ eval1 ctx t
eval1 ctx (Let t1 t2) = return$ maybe (termSubstTop t1 t2) (\t1'->Let t1' t2)$ eval1 ctx t1
eval1 ctx (Proj (Rec mp) field) = Data.Map.lookup field$ fmap (eval ctx) mp --一度にevalしている
eval1 ctx (Vari label term) = liftM (Vari label)$ eval1 ctx term
eval1 ctx (Case (As (Vari label term) typ) mp) | term'==Nothing = Data.Map.lookup label mp>>=(\t->return$termSubstTop term t)
  where term' = eval1 ctx term
eval1 ctx (Case term mp) = eval1 ctx term>>=(\term'->return$ Case term' mp)
eval1 ctx (Unfold type1 (Fold type2 v)) | v'==Nothing = return v
  where v' = eval1 ctx v
eval1 ctx (Fold typ t) = eval1 ctx t >>= return. Fold typ
eval1 ctx (Unfold typ t) = eval1 ctx t >>= return. Unfold typ
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
termSubst j s (If t1 t2 t3) = If (termSubst j s t1) (termSubst j s t2) (termSubst j s t3)
termSubst j s (Succ t) = Succ (termSubst j s t)
termSubst j s (Pred t) = Pred (termSubst j s t)
termSubst j s (IsZero t) = IsZero (termSubst j s t)
termSubst j s (Var k) | k==j = s
                      | otherwise = Var k
termSubst j s (Abs typ t) = Abs typ$ termSubst (j+1) (termShift 1 s) t
termSubst j s (App t1 t2) = App (termSubst j s t1) (termSubst j s t2)
termSubst j s (As t typ) = As (termSubst j s t) typ
termSubst j s (Let term t) = Let (termSubst j s term)$ termSubst (j+1) (termShift 1 s) t
termSubst j s (Rec mp) = Rec$ fmap (termSubst j s) mp
termSubst j s (Vari l t) = Vari l (termSubst j s t)
termSubst j s (Case typ mp) = Case (termSubst j s typ)$ fmap (termSubst (j+1) (termShift 1 s)) mp
termSubst j s (Proj t field) = Proj (termSubst j s t) field
termSubst j s (Fold typ t) = Fold typ (termSubst j s t)
termSubst j s (Unfold typ t) = Unfold typ (termSubst j s t)
termSubst j s t = t

--sをtに代入
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
    (headt1, bodyt1) <- reveal typet1
    if typet2 <: headt1 then return bodyt1 else throwError$ TypeMismatch (show typet2) headt1
  where 
        reveal (Arr t1 t2) = return (t1, t2)
        reveal t = throwError$ TypeMismatch "Arrow type" t
typeof ctx Unit = return TUnit
typeof ctx (Let t1 t2) = do
    typet1 <- typeof ctx t1
    typet2 <- typeof (typet1:ctx) t2
    return typet2
typeof ctx (Rec mp) = liftM Record$ T.mapM (typeof ctx) mp
typeof ctx (Proj (Rec mp) field) = case Data.Map.lookup field mp of
                                     Nothing->throwError$ FieldNotFound field
                                     Just val->typeof ctx val
typeof ctx (Case t0 mp) = do
    (Variant t0type)<- typeof ctx t0
    (T.mapM (\(label, term)->case Data.Map.lookup label t0type of
                                        Nothing->throwError$ LabelNotFound label
                                        Just ty->typeof (ty:ctx) term
                          )$ toList mp) >>= (\xs->maybe (return (xs!!0)) (throwError)$ getFirst$ foldMap First$ zipWith (\a b->if a==b then Nothing else Just(TypeMismatch (show a) b)) xs (tail xs))
typeof ctx (As vari@(Vari label term) ty@(Variant mp)) = case Data.Map.lookup label mp of
                                                        Nothing->throwError$ FieldNotFound label
                                                        Just typ->typeof ctx term>>=(\x->if x==typ then return ty else throwError$ TypeMismatch (show typ) x)
typeof ctx (As t ty) = do
    tty <- typeof ctx t
    if tty==ty then return ty else throwError$ TypeMismatch (show ty) tty
{-typeof ctx (Fold mu@(Mu x type1) t) = do
    typet <- typeof ctx t
    if typet == replaceTVar x mu type1 then return mu else throwError$ TypeMismatch "folding" mu
    -}
typeof ctx (Fold mu@(Mu x t) term) = do
    typet <- typeof ctx term
    return$ Main.fold mu typet 
typeof ctx (Unfold mu@(Mu x t) term) = do
    typet <- typeof ctx term
    return$ unfold mu typet 
--    if typet == unfold mu typet then return mu else throwError$ TypeMismatch "uhyohyo" mu


typeof ctx _ = throwError$ Default "no pattern matched"

(<:) :: Type->Type->Bool
_ <: Top = True
x <: y|x==y = True
(Arr s1 s2) <: (Arr t1 t2) = t1 <: s1 && s2 <: t2
(Record m1) <: (Record m2) = and$Prelude.map (\(k2,v2)->Data.Map.lookup k2 m1==Just v2)(toList m2)
_ <: _ = False

fold::Type->Type->Type
fold mu@(Mu varname typ) body = Mu varname $replace mu (TVar varname) body
unfold::Type->Type->Type
unfold mu@(Mu varname typ) (Mu varname2 body) = replace (TVar varname) mu body

fixN typ = (Abs (Arr typ typ)
            (App (Abs (Mu "A" (Arr (TVar "A") typ))
                      (Var 1 `App` (Unfold (Mu "A" (Arr (TVar "A") typ)) (Var 0) `App` Var 0)))
                 (Fold (Mu "A" (Arr (TVar "A") typ))
                       (Abs (Mu "A" (Arr (TVar "A") typ))
                            (Var 1 `App` (Unfold (Mu "A" (Arr (TVar "A") typ)) (Var 0) `App` Var 0))))))
fixV = (Abs (Arr (TVar "T") (TVar "T"))
            (App (Abs (Mu "A" (Arr (TVar "A") (TVar "T")))
                      (Var 1 `App` Abs (Mu "A" (TVar "A")) (Var 1 `App` Unfold (Mu "A" (Arr (TVar "A") (TVar "T"))) (Var 1) `App` Var 0)))
                 (Fold (Mu "A" (Arr (TVar "A") (TVar "T")))
                       (Abs (Mu "A" (Arr (TVar "A") (TVar "T")))
                            (Var 1 `App` (Abs (Mu "A" (TVar "A")) (Var 1 `App` Unfold (Mu "A" (Arr (TVar "A") (TVar "T"))) (Var 1) `App` Var 0)))))))

hungryt = Mu "A" (Arr Nat (TVar "A"))
--hungryf = Abs (Arr Nat (Mu "A" (Arr Nat (TVar "A")))) (Abs Nat (Fold (Mu "A" (Arr Nat (TVar "A"))) (Abs Nat (Fold (Mu "A" (Arr Nat (TVar "A"))) (Var 2)))))
--hungryf = Abs (Arr Nat (Mu "A" (Arr Nat (TVar "A")))) (Fold (Mu "A" (Arr Nat (TVar "A"))) (Abs Nat (Fold (Mu "A" (Arr Nat (TVar "A"))) (Abs Nat (Fold (Mu "A" (Arr Nat (TVar "A"))) (Var 2))))))
hungryf = (Abs (Arr Nat hungryt)
               (Abs Nat (Fold hungryt (Var 1))))

hungry = fixN (Arr Nat hungryt) `App` hungryf

inc=(Abs (Variant$ Data.Map.insert "just" Nat$ Data.Map.insert "nothing" TUnit empty) (Case (Var 0) $Data.Map.insert "just" (Succ (Var 0))$ Data.Map.insert "nothing" Zero empty))
just1 = Vari "just" (Succ Zero) `As` Variant (Data.Map.insert "just" Nat$ Data.Map.insert "nothing" TUnit empty)
