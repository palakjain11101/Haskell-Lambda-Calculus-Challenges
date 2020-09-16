-- comp2209 Functional Programming Challenges
-- (c) University of Southampton 2019
-- Skeleton code to be updated with your solutions
-- The dummy functions here simply return a randome value that is usually wrong 

-- DO NOT MODIFY THE FOLLOWING LINES OF CODE
module Challenges (alphaNorm, countAllReds, printLambda, parseLet, letToLambda,
    LamExpr(LamApp, LamAbs, LamVar), LetExpr(LetApp, LetDef, LetFun, LetVar, LetNum),
    lambdaToLet) where

-- Import standard library and parsing definitions from Hutton 2016, Chapter 13
import Data.Char
import Parsing

-- abstract data type for simple lambda calculus expressions
data LamExpr = LamApp LamExpr LamExpr  |  LamAbs Int LamExpr  |  LamVar Int deriving (Show, Eq)

-- abstract data type for simple let expressions
data LetExpr = LetApp LetExpr LetExpr  |  LetDef [([Int], LetExpr)] LetExpr |  LetFun Int | LetVar Int | LetNum Int deriving (Show, Eq)
-- END OF CODE YOU MUST NOT MODIFY


-- ADD YOUR OWN CODE HERE
-- Challenge 1
-- generate the alpha normal form for a simple lambda calculus expression
-- each bound variable is chosen to be the first one possible

--Pattern matching used to identify each type of expression and produce its Alpha normal form
alphaNorm :: LamExpr -> LamExpr
alphaNorm (LamVar a) = (LamVar a)
alphaNorm (LamApp e1 e2) = (LamApp (alphaNorm e1) (alphaNorm e2))
--alphaReduce is called only if the expression is in the form of a lambda abstraction
alphaNorm (LamAbs x e) = alphaReduce 0 [] (LamAbs x e)

{-the alpha reduction function takes as input the current value of the counter, a list of tuples
 each containing a non-free variable in the expression as well as the counter value they are being replaced with
 and returns the resulting lambda expression(also the output of alphaNorm) -}

--counter value starts at 0 as defined in the coursework specification
alphaReduce :: Int -> [(Int,Int)] -> LamExpr -> LamExpr

--Look for Lamdavariable a in the (non-free variable, counter) tuple list, if appears in the list replace it with its
--respective counter value,otherwise return the lambda variable as it is 
alphaReduce counter xs (LamVar a) | length (filter ((==a).fst) xs) /= 0 = LamVar (snd(head(filter ((==a).fst) xs)))
                                  | otherwise = LamVar a

--function is recursively called on each expression in LamApp
alphaReduce counter xs (LamApp e1 e2) = (LamApp (alphaReduce counter xs e1) (alphaReduce counter xs e2))

--if a is not free in the expression leave counter value as it is and recurse through it without increasing the counter
--if a is not free in the expression leave counter value as it is but increase it by 1 for the next part of the expression
alphaReduce counter xs (LamAbs a e) | not(free a e) = LamAbs(counter) (alphaReduce counter xs e)
                                    | otherwise = LamAbs(counter) ((alphaReduce (counter + 1) ((a,counter):xs) e))

--free function was provided in lecture slides
--given a number check whether it is free in the expression or not (returs true if free)
free :: Int -> LamExpr -> Bool
free x (LamVar y) = x == y
free x (LamAbs y e)
  | x == y = False
  | x /= y = free x e
free x (LamApp e1 e2) = (free x e1) || (free x e2)






-- Challenge 2
-- count all reduction paths for a given lambda expression m, of length up to a given limit l

-- returns number of expressions in beta normal form upon reaching the maximum limit  
countAllReds :: LamExpr -> Int -> Int
countAllReds e 0 = 0
countAllReds e n = length [x | x <- (newReductions (n-1) [e]), isBNF(x)]

-- recursively calls reduceExpression to get the list of expressions after each reduction
-- repeats this for the maximum number of times specified in the function
-- use of monadic parser allows xs to to replaced by new results in each iteration
-- only the end list is returned to countAllReds at the end
newReductions :: Int -> [LamExpr] -> [LamExpr]
newReductions 0 zs = zs
newReductions n zs = newReductions (n-1) (zs >>= reduceExpression)  


--checks whether an expression is in beta normal form
--a LamVar is already in beta normal form
isBNF :: LamExpr -> Bool
isBNF (LamApp (LamAbs x m) n) = False
isBNF (LamApp m n) = (isBNF m) && (isBNF n)
isBNF (LamAbs x m) = isBNF m
isBNF (LamVar x) = True    

-- takes an expression as input and return all possible 1 step reductions of the original expression
reduceExpression :: LamExpr -> [LamExpr]

--if solution is in beta normal form, it cannot be reduced further so return the original list
reduceExpression e | isBNF e = [e]

--if the expression is an application of a lambda expression and another expression, substitute e2 for every free variable x in e1
--if e2 is also reducible, perform outer reduction as well and append the resulting lists of both reductions
--function map applies the outerexpression of the pattern matching expression to each reduced expression in the second list
reduceExpression (LamApp (LamAbs x e1) e2) = [substitute e1 x e2] ++ [e | e <- (map (outerExpression a) (reduceExpression e2)), (isBNF(e) || (e /= a))]
        where outerExpression (LamApp e1 e2) e = (LamApp e1 e)
              a = (LamApp (LamAbs x e1) e2)

--if the expression is a simple lambda abstraction it is not reducible
--but if expression e can be reduced, add it reduced form to the list
reduceExpression (LamAbs x e) = map (abstractExpression a) (reduceExpression e)
        where abstractExpression (LamAbs x e1) e2 = LamAbs x e2
              a = (LamAbs x e)

--given simply an application, perform reduction on each expression 
reduceExpression (LamApp e1 e2) = [e | e <- ((map (firstExpression a) (reduceExpression e1)) ++ (map (secondExpression a) (reduceExpression e2))), isBNF(e) || (e /= a)] 
        where secondExpression (LamApp e1 e2) e = (LamApp e1 e)
              firstExpression (LamApp e1 e2) e = (LamApp e e2)
              a = (LamApp e1 e2)


--Note: substitute method used was provided in lecture slides                                                                
substitute :: LamExpr -> Int ->  LamExpr -> LamExpr
substitute (LamVar n) m e | n == m = e
substitute (LamVar n) m e | n /= m = LamVar n
substitute (LamAbs n e1) m e  | n /= m && not (free n e)  = LamAbs n (substitute e1 m e)
substitute (LamAbs n e1) m e  | n /= m &&     (free n e)  = substitute (LamAbs (n+1) (substitute e1 n (LamVar (n+1)))) m e
substitute (LamAbs n e1) m e  | n == m  = LamAbs n e1
substitute (LamApp e1 e2) m e = LamApp (substitute e1 m e) (substitute e2 m e) 






-- Challenge 3 
-- pretty print a lambda expression, combining abstraction variables
-- also recognising Scott numerals and printing these as numbers
-- finalising omitting brackets where possible and safe to do so
printLambda :: LamExpr -> String

--for a simple lambda variable show x
printLambda (LamVar x) = "x"++ show x

-- for an application following abstractions check for the scott encoding
-- if a scott encoding exists for the expression and if the value of z matches the 
-- encoding, return the next scott encoding(natural number)
-- otherwise just print the expression 
printLambda (LamAbs w (LamAbs x (LamApp (LamVar y) z))) 
            | let a = (LamApp (LamVar y) z) in (checkScottNumeral2 x a && printLambda z == "1") = "2"
            | let b = (LamApp (LamVar y) z) in (checkScottNumeral2 x b && printLambda z == "0") = "1"
            | let d = (LamApp (LamVar y) z) in (checkScottNumeral2 x d && printLambda z == "getInt(s)") = "getInt(s)+1"
            | otherwise = printExpression (LamAbs w c)
                where c = (LamAbs x (LamApp (LamVar y) z))

-- for an expression of the following pattern check if the scott encoding is 0
-- if the scott encoding is 0, print 0, otherwise print the expression 
printLambda (LamAbs x (LamAbs y z))
            | checkScottNumeral1 x z = "0"
            | otherwise = printExpression (LamAbs x a)
                  where a = (LamAbs y z)

--the scott encoding does not exist for all three patterns so the expression can be printed safely
printLambda (LamAbs x t) = "\\" ++ "x" ++ show x ++ " -> " ++ printLambda t

printLambda (LamApp (LamAbs x e) t) = "(" ++ printLambda (LamAbs x e) ++ ") " ++ printLambda t

printLambda (LamApp y t) =  printLambda y ++ " " ++ printLambda t


--helper function to print lambda abstraction
printExpression :: LamExpr -> String
printExpression (LamAbs x t) = "\\" ++ "x" ++ show x ++ " -> " ++ printLambda t

--checks if expression is equivalant to scott number 1
checkScottNumeral1 ::Int -> LamExpr -> Bool
checkScottNumeral1 a (LamVar x) | (a == x) = True 
                                | otherwise = False

--checks if expression is equivalant to scott number 2
checkScottNumeral2 :: Int -> LamExpr -> Bool
checkScottNumeral2 y (LamApp (LamVar z) t) | let x = (LamVar z) in checkScottNumeral1 y x = True 
                                           | otherwise = False

--retrieves the scott encoding in numeric form
getInt :: Char -> Int
getInt x = digitToInt x






-- Challenge 4
-- parse recursive let expression, possibly containing numerals
parseLet :: String -> Maybe LetExpr

--Some functions in challenge 4 have been adapted from the parsing lecture
parseLet string = helperParseLet string

-- helper function to test for valid let expressions
helperParseLet string =
    let xs = parse expression string in
-- if parsing failed then return no value
      if xs == [] then Nothing
      else let [(e,string')] = xs in 
-- the string must be fully consumed in parsing
        if string' /= "" then Nothing      
-- return the expression converted to the corresponding abstract data type
        else Just e

--identifier looks for character 'x' to help parse it as a variable
variableIdentifier :: Parser Int
variableIdentifier =
    do space
       char 'x'
       n <- nat
       space
       return n

--identifer looks for character 'f' to help parse it as a function
functionIdentifier :: Parser Int
functionIdentifier =
    do space
       char 'f'
       n <- nat
       space
       return n

--function to parse any number in LetExpr datatype as LetNum
number :: Parser LetExpr
number = 
    do n <- nat
       return (LetNum n)

--looks for an identifier 'x' preceding n and returns a LamVar 
variable :: Parser LetExpr
variable = 
    do n <- variableIdentifier
       return (LetVar n)

--looks for an identifier 'f' preceding n and returns a LamFunc
function :: Parser LetExpr
function = 
    do n <- functionIdentifier
       return (LetFun n)

--function to parse the first equation in a let expression
equation = do  ys <- functionIdentifier
               ns <- variableIdentifier
               symbol "="
               e1 <- expression
               return ([ys]++[ns], e1)

--function to parse the initial equation as well as a list of equations following a semi-colon in a let expression
equationList = do x <- equation
                  ys <- many (do symbol ";"; y <- equation; return y)
                  return ([x]++(ys))

--identifies a let expression, retrieves all the equations, places tem accordingly and returns let expression
letDefinition :: Parser LetExpr
letDefinition =
    do symbol "let"
       e1 <- equationList
       symbol "in"
       e2 <- expression
       return (LetDef e1 (e2))

-- recognise an application
application :: Parser LetExpr
application = 
     -- recognise a list of expressions, foldl1 is used to maintain left associativity
     do xs <- some lowerExpression
        return (foldl1 (\e1 -> \e2 -> LetApp e1 e2) xs)

--application is at highest priority in parsing
expression :: Parser LetExpr
expression = application <|> lowerExpression

-- used recognise other types of expressions which are all at the same priority
lowerExpression :: Parser LetExpr
lowerExpression =
     do symbol "("
        e <- expression
        symbol ")"
        return e 
     <|> variable
     <|> letDefinition
     <|> function
     <|> number



-- Challenge 5
-- translate a let expression into lambda calculus, using Scott numerals
-- convert let symbols to lambda variables using Jansen's techniques rather than Y
letToLambda :: LetExpr -> LamExpr
letToLambda _ = LamVar (-1)


-- Challenge 6
-- convert a lambda calculus expression into one using let expressions and application
-- can use lambda lifting techniques described in wikipedia article
lambdaToLet :: LamExpr -> LetExpr
lambdaToLet _ = LetVar (-1)