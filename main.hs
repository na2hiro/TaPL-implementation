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
          | Abs VarName Type Term
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
             | FieldNotFound FieldName Type
             | LabelNotFound Label Type
             | Default String

type TypeName = String
type FieldName = String
type TypeVarName = String
type Label = String
type VarName = String

instance Error MyError where
    noMsg = Default "An error has occurred"
    strMsg = Default

showError :: MyError -> String
showError (Default str) = str
showError (TypeMismatch expected found) = "Invalid type: expected "++ expected ++ ", found "++show found
showError (FieldNotFound field record) = "Field '"++field++"' not found on record typed "++show record
showError (LabelNotFound label variant) = "Label '"++label++"' not found on variant typed "++show variant

type VarNameContext = [VarName]

showTerm :: VarNameContext -> Term -> String
showTerm _ Tru = "true"
showTerm _ Fals = "false"
showTerm ctx (If a b c) = "if "++showTerm ctx a++" then "++showTerm ctx b++" else "++showTerm ctx c
showTerm _ Zero = "zero"
showTerm ctx (Succ t) = "succ "++showTerm ctx t
showTerm ctx (Pred t) = "pred "++showTerm ctx t
showTerm ctx (IsZero t) = "iszero "++showTerm ctx t
showTerm ctx (Var i) = ctx!!i
showTerm ctx (Abs varn typ term) = "(\\"++varn++":"++show typ++"."++showTerm (varn:ctx) term++")"
showTerm ctx (App t1 t2) = "("++showTerm ctx t1++" "++showTerm ctx t2++")"
showTerm _ Unit = "unit"
showTerm ctx (As term typ) = showTerm ctx term++" as "++show typ
showTerm ctx (Let t1 t2) = "let "++showTerm ctx t1++" in "++showTerm ctx t2
showTerm ctx (Rec mp) = "{"++intercalate "," (Prelude.map (\(k,v)->k++"="++showTerm ctx v)$ toList mp)++"}"
showTerm ctx (Proj t name) = showTerm ctx t++"."++name
showTerm ctx (Vari label term) = "<"++label++"="++showTerm ctx term++">"
showTerm ctx (Case term mp) = "case "++showTerm ctx term++" of "++(intercalate " | "$ Prelude.map (\(label,t)->label++"=>"++showTerm ctx t)$ toList mp)
showTerm ctx (Fold typ term) = "fold ["++show typ++"] "++showTerm ctx term
showTerm ctx (Unfold typ term) = "unfold ["++show typ++"] "++showTerm ctx term

instance Show Term where show = showTerm []

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

replace::Type->Type->Type->Type
replace from to val | val==from = to
replace from to (Arr t1 t2) = Arr (replace from to t1) (replace from to t2)
replace from to (Record mp) = Record$ fmap (replace from to) mp
replace from to (Variant mp) = Variant$ fmap (replace from to) mp
replace (TVar varname) to mu@(Mu varname2 body) | varname==varname2 = mu
replace from to (Mu varname body) = Mu varname (replace from to body)
replace _ _ body = body 

eval1 :: Context->Term->Maybe Term
eval1 ctx (If Tru t _) = Just t -- E-IfTrue 3-1
eval1 ctx (If Fals _ t) = Just t -- E-IfFalse 3-1
{-
eval1 (If t b c) | isJust new = new >>= (\newt->Just$ If newt b c)
  where new = eval1 t
-}
eval1 ctx (If t b c) = eval1 ctx t >>= (\newt->Just$ If newt b c) -- E-If 3-1
eval1 ctx (Succ t) = eval1 ctx t >>= Just. Succ -- E-Succ 3-2
eval1 ctx (Pred Zero) = Just Zero -- E-PredZero 3-2
eval1 ctx (Pred (Succ n)) = Just n -- E-PredSucc 3-2
eval1 ctx (Pred t) = eval1 ctx t >>= Just. Pred -- E-Pred 3-2
eval1 ctx (IsZero Zero) = Just Tru -- E-IsZeroZero 3-2
eval1 ctx (IsZero (Succ n)) = Just Fals -- E-IsZeroSucc 3-2
eval1 ctx (IsZero t) = eval1 ctx t >>= Just. IsZero -- E-IsZero 3-2
eval1 ctx (App t1 t2) | isJust t1' = t1' >>= \t1'->Just$ App t1' t2 -- E-App1 5-3
                      | isJust t2' = t2' >>= \t2'->Just$ App t1 t2' -- E-App2 5-3
  where t1'=eval1 ctx t1
        t2'=eval1 ctx t2
eval1 ctx (App (Abs varn typ x) t2) = Just$ termSubstTop t2 x -- E-AppAbs 5-3
eval1 ctx (As t ty) = case t of
                        Vari label term -> eval1 ctx term >>= (\term'->return$As (Vari label term') ty)
                        otherwise -> maybe (return t) (\t'->return$ As t' ty)$ eval1 ctx t -- E-Ascribe 11-3
eval1 ctx (Let t1 t2) = return$ maybe (termSubstTop t1 t2) (\t1'->Let t1' t2)$ eval1 ctx t1 -- E-LetV, E-Let 11-4
eval1 ctx (Proj term field) = case eval1 ctx term of
                                Just t'->Just$ Proj t' field -- E-Proj 11-7
                                Nothing->case term of
                                           Rec mp->Data.Map.lookup field mp -- E-ProjRcd 11-7
                                           otherwise->Nothing
eval1 ctx (Rec mp) = if b then return$ Rec$ fromList$ reverse xs else Nothing -- E-Rcd 11-7
  where step xs = Prelude.foldl f (False,[]) xs
        f (b,xs) x@(k,v) = if b then (b,x:xs) else maybe (b,x:xs) (\v'->(True,(k,v'):xs)) (eval1 ctx v)
        (b,xs) = step$ toList mp
eval1 ctx (Vari label term) = liftM (Vari label)$ eval1 ctx term -- E-Variant 11-11
eval1 ctx (Case (As (Vari label term) typ) mp) | term'==Nothing = Data.Map.lookup label mp>>=(\t->return$termSubstTop term t) -- E-CaseVariant 11-11
  where term' = eval1 ctx term
eval1 ctx (Case term mp) = eval1 ctx term>>=(\term'->return$ Case term' mp) -- E-Case 11-11
eval1 ctx (Unfold type1 (Fold type2 v)) | v'==Nothing = return v -- E-UnfoldFold 20-1
  where v' = eval1 ctx v
eval1 ctx (Fold typ t) = eval1 ctx t >>= return. Fold typ -- E-Fold 20-1
eval1 ctx (Unfold typ t) = eval1 ctx t >>= return. Unfold typ -- E-Unfold 20-1
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
        shift c (Abs varn typ t) = Abs varn typ$ shift (c+1) t
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
termSubst j s (Abs varn typ t) = Abs varn typ$ termSubst (j+1) (termShift 1 s) t
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
typeof ctx Tru = return Bool -- T-True 8-1
typeof ctx Fals = return Bool -- T-False 8-1
typeof ctx (If t1 t2 t3) = do -- T-If 8-1
    typet1 <- typeof ctx t1
    typet2 <- typeof ctx t2
    typet3 <- typeof ctx t3
    case typet1 == Bool of
      False->throwError$ TypeMismatch (show Bool) typet1
      True->case typet2 == typet3 of
        False->throwError$ TypeMismatch (show typet2) typet3
        True->return typet2
typeof ctx Zero = return Nat -- T-Zero 8-2
typeof ctx (Succ n) = do -- T-Succ 8-2
    typet <-typeof ctx n
    if typet==Nat then return Nat else throwError$ TypeMismatch (show Nat) typet
typeof ctx (Pred n) = do -- T-Pred 8-2
    typet <- typeof ctx n
    if typet==Nat then return Nat else throwError$ TypeMismatch (show Nat) typet
typeof ctx (IsZero n) = do -- T-IsZero 8-2
    typet <- typeof ctx n
    if typet==Nat then return Bool else throwError$ TypeMismatch (show Nat) typet
typeof ctx (Var x) = return (ctx!!x) -- T-Var 9-1
typeof ctx (Abs varn typevar t) = do -- T-Abs 9-1
    typet <- typeof (typevar:ctx) t
    return$ Arr typevar typet
typeof ctx (App t1 t2) = do -- T-App 9-1
    typet1 <- typeof ctx t1
    typet2 <- typeof ctx t2
    (headt1, bodyt1) <- reveal typet1
    if typet2 <: headt1 then return bodyt1 else throwError$ TypeMismatch (show typet2) headt1
  where 
        reveal (Arr t1 t2) = return (t1, t2)
        reveal t = throwError$ TypeMismatch "Arrow type" t
typeof ctx Unit = return TUnit -- T-Unit 11-2
typeof ctx (Let t1 t2) = do -- T-Let 11-4
    typet1 <- typeof ctx t1
    typet2 <- typeof (typet1:ctx) t2
    return typet2
typeof ctx (Rec mp) = liftM Record$ T.mapM (typeof ctx) mp -- T-Rcd 11-7
typeof ctx (Proj r field) = case typeof ctx r of -- T-Proj 11-7
                              Right rc@(Record mp)->case Data.Map.lookup field mp of
                                                   Nothing->throwError$ FieldNotFound field rc
                                                   Just typ->return typ
                              otherwise -> throwError$ Default$ "projecting non-record term: "++show r
typeof ctx (Case t0 mp) = do -- T-Case 11-11
    (Variant t0type)<- typeof ctx t0
    (T.mapM (\(label, term)->case Data.Map.lookup label t0type of
                                        Nothing->throwError$ LabelNotFound label (Variant t0type)
                                        Just ty->typeof (ty:ctx) term
                          )$ toList mp) >>= (\xs->maybe (return (xs!!0)) (throwError)$ getFirst$ foldMap First$ zipWith (\a b->if a==b then Nothing else Just(TypeMismatch (show a) b)) xs (tail xs))
typeof ctx (As vari@(Vari label term) ty@(Variant mp)) = case Data.Map.lookup label mp of -- T-Variant 11-11
                                                        Nothing->throwError$ LabelNotFound label ty
                                                        Just typ->typeof ctx term>>=(\x->if x==typ then return ty else throwError$ TypeMismatch (show typ) x)
typeof ctx (As t ty) = do -- T-Ascribe
    tty <- typeof ctx t
    if tty==ty then return ty else throwError$ TypeMismatch (show ty) tty
{-typeof ctx (Fold mu@(Mu x type1) t) = do
    typet <- typeof ctx t
    if typet == replaceTVar x mu type1 then return mu else throwError$ TypeMismatch "folding" mu
    -}
typeof ctx (Fold mu@(Mu x t) term) = do -- T-Fld 20-1
    typet <- typeof ctx term
    return$ Main.fold mu typet 
typeof ctx (Unfold mu@(Mu x t) term) = do -- T-Unfld 20-1
    typet <- typeof ctx term
    return$ unfold mu typet 
--    if typet == unfold mu typet then return mu else throwError$ TypeMismatch "uhyohyo" mu


typeof ctx term = throwError$ Default$ "no pattern matched: "++show term

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

fixN typ = (Abs "f" (Arr typ typ)
            (App (Abs "x" (Mu "A" (Arr (TVar "A") typ))
                      (Var 1 `App` (Unfold (Mu "A" (Arr (TVar "A") typ)) (Var 0) `App` Var 0)))
                 (Fold (Mu "A" (Arr (TVar "A") typ))
                       (Abs "x" (Mu "A" (Arr (TVar "A") typ))
                            (Var 1 `App` (Unfold (Mu "A" (Arr (TVar "A") typ)) (Var 0) `App` Var 0))))))
fixV = (Abs "f" (Arr (TVar "T") (TVar "T"))
            (App (Abs "x" (Mu "A" (Arr (TVar "A") (TVar "T")))
                      (Var 1 `App` Abs "y" (Mu "A" (TVar "A")) (Var 1 `App` Unfold (Mu "A" (Arr (TVar "A") (TVar "T"))) (Var 1) `App` Var 0)))
                 (Fold (Mu "A" (Arr (TVar "A") (TVar "T")))
                       (Abs "x" (Mu "A" (Arr (TVar "A") (TVar "T")))
                            (Var 1 `App` (Abs "y" (Mu "A" (TVar "A")) (Var 1 `App` Unfold (Mu "A" (Arr (TVar "A") (TVar "T"))) (Var 1) `App` Var 0)))))))

hungryt = Mu "A" (Arr Nat (TVar "A"))
hungryf = (Abs "f" (Arr Nat hungryt)
               (Abs "n" Nat (Fold hungryt (Var 1))))

hungry = fixN (Arr Nat hungryt) `App` hungryf

natList = Mu "X"$ Variant$ insert "nil" TUnit$ insert "cons" (Record$ insert "hd" Nat$ insert "tl" (TVar "X") empty) empty
nlBody = Variant$ insert "nil" TUnit$ insert "cons" (Record$ insert "hd" Nat$ insert "tl" natList empty) empty
nil = Fold natList (Vari "nil" Unit `As` nlBody)
cons = (Abs "n" Nat (Abs "l" natList (Fold natList (Vari "cons" (Rec$ insert "hd" (Var 1)$ insert "tl" (Var 0) empty) `As` nlBody))))
isnil = Abs "l" natList (Case (Unfold natList (Var 0)) (insert "nil" Tru$ insert "cons" Fals empty))
hd = Abs "l" natList$ Case (Unfold natList (Var 0))$ insert "nil" Zero$ insert "cons" (Proj (Var 0) "hd") empty
tl = Abs "l" natList$ Case (Unfold natList (Var 0))$ insert "nil" (Var 1)$ insert "cons" (Proj (Var 0) "tl") empty

inc=(Abs "x" (Variant$ insert "just" Nat$ insert "nothing" TUnit empty) (Case (Var 0) $insert "just" (Succ (Var 0))$ insert "nothing" Zero empty))
just1 = Vari "just" (Succ Zero) `As` Variant (insert "just" Nat$ insert "nothing" TUnit empty)
