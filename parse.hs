module Parse where
import Main
import Text.ParserCombinators.Parsec
import Control.Applicative((<*),(*>))
import Control.Monad
import Data.List(elemIndex)

parseExpr :: [String]->Parser Term
parseExpr ctx = parseBool <* spaces
            <|> parseIf ctx <* spaces
            <|> parseArith ctx <* spaces
            <|> parseLambda ctx <* spaces
-- 3-1
parseBool = string "true" *> return Tru
        <|> string "false" *> return Fals
-- 3-1
parseIf ctx = do
            string "if"
            t1<-spaces *> parseExpr ctx
            string "then"
            t2<-spaces *> parseExpr ctx
            string "else"
            t3<-spaces *> parseExpr ctx
            return$ If t1 t2 t3
-- 3-2
parseArith ctx = string "0" *> spaces *> return Zero
             <|> string "succ" *> spaces *> (parseExpr ctx>>= return. Succ)
             <|> string "pred" *> spaces *> (parseExpr ctx>>= return. Pred)
             <|> string "iszero" *> spaces *> (parseExpr ctx>>= return. IsZero)

-- 5-3
parseLambda ctx = parseAbs ctx
              <|> parseVar ctx

parseAbs ctx = do
        string "\\"
        var<-parseVarName
        string ":"
        typ<-parseType
        string "."
        term<-parseExpr (var:ctx)
        return$ Abs var typ term

parseVar ctx = do
            t<-many$ oneOf ['a'..'z']
            maybe (error ("free variable "++t++" found under context of "++show ctx)) (return. Var) (elemIndex t ctx)

parseVarName = many$ oneOf ['a'..'z']

parseType = string "Bool" *> return Bool

doParse :: String->Either ParseError Term
doParse = parse (spaces>>parseExpr []) "Term"
