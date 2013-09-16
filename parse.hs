module Parse where
import Main
import Text.ParserCombinators.Parsec
import Control.Applicative((<*),(*>))
import Control.Monad

parseExpr :: Parser Term
parseExpr = parseBool <* spaces
        <|> parseIf <* spaces
        <|> parseArith <* spaces
-- 3-1
parseBool = string "true" *> return Tru
        <|> string "false" *> return Fals
-- 3-1
parseIf = do
        string "if"
        t1<-spaces *> parseExpr
        string "then"
        t2<-spaces *> parseExpr
        string "else"
        t3<-spaces *> parseExpr
        return$ If t1 t2 t3
-- 3-2
parseArith = string "0" *> spaces *> return Zero
         <|> string "succ" *> spaces *> (parseExpr>>= return. Succ)
         <|> string "pred" *> spaces *> (parseExpr>>= return. Pred)
         <|> string "iszero" *> spaces *> (parseExpr>>= return. IsZero)

doParse :: String->Either ParseError Term
doParse = parse (spaces>>parseExpr) "Term"
