-- comp2209 Functional Programming Challenges
-- (c) University of Southampton 2019
-- Author:Palak Jain

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





-- Challenge 1
-- generate the alpha normal form for a simple lambda calculus expression
-- each bound variable is chosen to be the first one possible

--Pattern matching used to identify each type of expression and produce its Alpha normal form
alphaNorm :: LamExpr -> LamExpr
alphaNorm (LamVar a) = (LamVar a)
alphaNorm (LamApp e1 e2) = (LamApp (alphaNorm e1) (alphaNorm e2))
alphaNorm a@(LamAbs x e) = (alphaReduce 0 [] (LamAbs x e))


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
alphaReduce counter xs (LamAbs a e) | ((free a e) == False) = LamAbs(counter) (alphaReduce counter xs e)
                                    | otherwise = LamAbs(counter) ((alphaReduce (counter + 1) ((a,counter):xs) e))


--free function was provided in lecture 13
--given a number check whether it is free in the expression or not (returns true if free)
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


--takes an expression as input and return all possible 1 step reductions of the original expression
reduceExpression :: LamExpr -> [LamExpr]

--if solution is in beta normal form, it cannot be reduced further so return the original list
reduceExpression e | isBNF e = [e]

{-if the expression is an application of a lambda expression and another expression, 
substitute e2 for every free variable x in e1 -}
--if e2 is also reducible, perform outer reduction as well and append the resulting lists of both reductions
{-function map applies the outerexpression of the pattern matching expression to each reduced expression in 
the second list-}
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


--Note: substitute function was provided in lecture 13                                                               
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
{- if a scott encoding exists for the expression and if the value of z matches the 
 encoding, return the next scott encoding(natural number)
 otherwise just print the expression -}
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


--checks if expression is equivalant to scott number 0
checkScottNumeral1 ::Int -> LamExpr -> Bool
checkScottNumeral1 a (LamVar x) | (a == x) = True 
                                | otherwise = False


--checks if expression is equivalant to scott number 0
checkScottNumeral2 :: Int -> LamExpr -> Bool
checkScottNumeral2 y (LamApp (LamVar z) t) | let x = (LamVar z) in checkScottNumeral1 y x = True 
                                           | otherwise = False


--retrieves the scott encoding in numeric form
getInt :: Char -> Int
getInt x = digitToInt x






-- Challenge 4
-- parse recursive let expression, possibly containing numerals
parseLet :: String -> Maybe LetExpr


{-some functions in challenge 4 have been adapted from the parsing lecture and the code from parsing example
in the course notes secion of the module page-}
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


--function to parse the initial equation as well as a list of equations following a semi-colon 
--in a let expression
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

{- Note: letToLambda function returns a lambda expression without performing alpha reduction.
   This is to ensure that any bugs from challenge 1 do not affect the results of challenge 5.
   The additional tests developed for Challenge 5 (in Tests.hs) however, are in alpha normal form. This ensures consistency and uniformity in the tests.
-}

letToLambda :: LetExpr -> LamExpr
letToLambda (LetFun x) = (LamVar (x+1000))
letToLambda (LetVar x) = (LamVar (x))
letToLambda q = (modifyLet q)
--In order to derive the alpha normal form of the resulting expression, one can substitute the above equation with: letToLambda q = alphaNorm(modifyLet q)


{- calls function createLamExpr on let expression with all (LetFun x) expressions replaced with 
(LetFun (x+1000)) so that LetFun x is not confused with LetVar x when converted to LamVar -}
--since x in list xs is also a function, it is incremented by 1000
modifyLet :: LetExpr -> LamExpr
modifyLet (LetDef[((x:xs), y), ((a:as), b)] (z)) = createLamExpr(LetDef[(((x+1000):xs), (modifyLet1 x a y)), (((a+1000):as), (modifyLet1 x a b))] (modifyLet1 x a z))
modifyLet (LetDef[((x:xs), y)] (z)) = createLamExpr(LetDef[(((x+1000):xs), (modifyLet1 x x y))] (modifyLet1 x x z))


modifyLet1 :: Int -> Int -> LetExpr -> LetExpr
modifyLet1 m n (LetVar x) = (LetVar x)
modifyLet1 m n (LetFun y) | y == m = (LetFun (y+1000))
                          | y == n = (LetFun (y+1000))
                          | otherwise = (LetFun y)
modifyLet1 m n (LetNum z) = (LetNum z)
modifyLet1 m n (LetApp a b) = (LetApp (modifyLet1 m n a) (modifyLet1 m n b))


--constructs the LamExpr from LetExpr by calling function checkZ and checkZ1 respectively
createLamExpr :: LetExpr -> LamExpr
createLamExpr (LetDef[((x:xs), y)] (z)) = (checkZ z (x:xs) y)
createLamExpr (LetDef[((x:xs), y), ((a:as), b)] (z)) = (checkZ1 z (x:xs) y (a:as) b)


--the three functions below handle expressions of form let f x = e in d

--in the occurrence of f in d the whole expression fPrime is applied to itself
--also constructs fPrime by calling function createfPrime
checkZ :: LetExpr -> [Int] -> LetExpr -> LamExpr
checkZ (LetVar a) (x:xs) y = (LamVar a)
checkZ (LetFun a) (x:xs) y | (a == x) = (LamApp(createfPrime (x:xs) y x) (createfPrime (x:xs) y x))
                           | otherwise = (LamVar a)
checkZ (LetApp a b) (x:xs) y = (LamApp (checkZ a (x:xs) y) (checkZ b (x:xs) y))


--all parts to the left of "=" sign are turned to abstractions
createfPrime :: [Int] -> LetExpr -> Int -> LamExpr
createfPrime [] y a = (createApps (getNumbers(y)) a (LamVar a))
createfPrime (x:xs) y a = (LamAbs x (createfPrime xs y a))


{-constructs expression e similar to the construction of d, but in this case the application is only 
performed on a LetFun rather than the whole expression-}
createApps :: [Int] -> Int -> LamExpr -> LamExpr
createApps [] a e  = e
createApps [x] a e |(x == a) = LamApp(LamVar x) (LamVar x)
                   |otherwise = LamVar x
createApps (x:xs) a e = (LamApp (createApps [x] a e) (createApps (xs) a e))


--the three functions below handle expressions of form let f x = e; g y = h in d

{-in the occurrence of f in d the whole expression fPrime is applied to itself and the result is applied 
to gPrime
in the occurrence of g in d the whole expression gPrime is applied to fPrime and the result is applied 
to gPrime -}
--also constructs expressions fPrime and gPrime by calling function createfgPrime with the corresponding arguments
checkZ1 :: LetExpr -> [Int] -> LetExpr -> [Int] -> LetExpr -> LamExpr
checkZ1 (LetVar a) (x:xs) y (r:rs) t = (LamVar a)
checkZ1 (LetFun a) (x:xs) y (r:rs) t | (a == x) = (LamApp (LamApp fPrime fPrime) gPrime)
                                     | (a == r) = (LamApp (LamApp gPrime fPrime) gPrime)
                                     | otherwise = (LamVar a)
                                              where fPrime = (createfgPrime (x:r:xs) y x r)
                                                    gPrime = (createfgPrime (x:r:rs) t x r)
checkZ1 (LetApp a b) (x:xs) y (r:rs) t = (LamApp (checkZ1 a (x:xs) y (r:rs) t) (checkZ1 b (x:xs) y (r:rs) t))


{-first abstraction is always f, second abstraction is g, the rest are dependant on the arguments of 
--f or g before the the "=" sign-}
createfgPrime :: [Int] -> LetExpr -> Int -> Int -> LamExpr
createfgPrime [] y a b = (createApps1 (getNumbers y) a b (LamVar a))
createfgPrime (x:xs) y a b = (LamAbs x (createfgPrime xs y a b))

                                         
--constructs expressions e and h similar to the construction of d, but in this case 
--the application is only performed on a LetFun
createApps1 :: [Int] -> Int -> Int ->  LamExpr -> LamExpr
createApps1 [] a b e  = e
createApps1 [x] a b e |(x == a) = (LamApp (LamApp (LamVar a) (LamVar a)) (LamVar b))  
                      |(x == b) = (LamApp (LamApp (LamVar b) (LamVar a)) (LamVar b))
                      |otherwise = LamVar x
createApps1 (x:y:xs) a b e = (LamApp (LamApp (createApps1 [x] a b e) (createApps1 [y] a b e)) (createApps1 (xs) a b e))


--returns the number associated with a simple LetExpr 
--used to create applications                  
getNumbers :: LetExpr -> [Int]
getNumbers (LetVar x) = [x]
getNumbers (LetFun y) = [y]
getNumbers (LetNum z) = [z]
getNumbers (LetApp a b) = getNumbers a ++ getNumbers b





-- Challenge 6
-- convert a lambda calculus expression into one using let expressions and application
-- can use lambda lifting techniques described in wikipedia article
lambdaToLet :: LamExpr -> LetExpr
lambdaToLet e = LetDef(createPart1 0 (checkAbstractions e [])) (createPart2 0 e)


--returns part1 of answer
--functionNumber is given the initial value 0; for each abstraction in the original expression, functionNumber is incremented
--each time take functionNumber and one abstraction from the list and concatenatinate the functionNumber with the arguments of the lambda lifted abstraction, convert body of abstraction to expression
createPart1 :: Int -> [LamExpr] -> [([Int], LetExpr)]
createPart1 functionNumber [(LamAbs a b)] = [(([functionNumber] ++ (lambdaLift (LamAbs a b))), (lamToLet functionNumber b))]
createPart1 functionNumber (x:xs) = (createPart1 functionNumber [x]) ++ (createPart1 (functionNumber+1) (xs)) 


--used patternmatching to identify LamExpr and convert it to LetExpr
createPart2 :: Int -> LamExpr -> LetExpr
createPart2 functionNumber (LamAbs x e)  | ((lamFree e) == True) = (LetFun functionNumber)
                                         | otherwise = (LetFun ((length(checkAbstractions (LamAbs x e) []) - 1) + functionNumber))
createPart2 functionNumber (LamVar x) = (LetVar x)
createPart2 functionNumber (LamApp e1 e2) | (lamFree e1) && (lamFree e2) = (LetApp (createPart2 functionNumber e1) (createPart2 functionNumber e1))
                                          | otherwise = (LetApp (createPart2 functionNumber e1) (createPart2 (length(checkAbstractions e1 [])) e2))


--checks whether the expression has an abstraction or not
lamFree :: LamExpr -> Bool
lamFree (LamVar x) = True
lamFree (LamAbs x b) = False
lamFree (LamApp x y) = (lamFree x) && (lamFree y)


--finds all abstractions in a LamExpr and puts them in a list
--Deepest abstraction appears first in the list
checkAbstractions :: LamExpr -> [LamExpr] -> [LamExpr]
checkAbstractions (LamApp a b) xs = (checkAbstractions a xs) ++ (checkAbstractions b xs)
checkAbstractions (LamAbs a b) xs = (checkAbstractions b xs) ++ [(LamAbs a b)]
checkAbstractions (LamVar a) xs = []


--converts body of abstraction to let expression
lamToLet :: Int -> LamExpr -> LetExpr
lamToLet num e@(LamVar x) = LetVar x 
lamToLet num e@(LamAbs x b) | (length xs > 0) =  (lamToLet num (lambdaConverter e xs))
                            | otherwise = (LetFun (num - 1))
                                where xs = [x |x <- (getNumbers1 e), free x e] 
lamToLet num e@(LamApp x y) = LetApp (lamToLet num x) (lamToLet num y)


--retrieves all free Lambda variables in the expression 
--if there are free variables, lambdaLift1 constucts a new expression performing lambda lifting
--otherwise leave expression as it is
lambdaLift :: LamExpr -> [Int]
lambdaLift e@(LamAbs a b) = (lambdaLift1 e [x |x <- (getNumbers1 e), free x e])


lambdaLift1 :: LamExpr -> [Int] -> [Int]
lambdaLift1 e (xs) | (length(xs) /= 0) = checkLamLifting (LamApp (absCreate1 xs e) (appCreate1 xs)) e
                   | otherwise = checkLamLifting (e) e
lambdaConverter e (xs) = (LamApp (absCreate1 xs e) (appCreate1 xs))


--retrieves all Lambda variables and replaces them with list of integers that they correspond to
getNumbers1 :: LamExpr -> [Int]
getNumbers1 (LamVar x) = [x]
getNumbers1 (LamAbs a b) = getNumbers1 b
getNumbers1 (LamApp a b) = getNumbers1 a ++ getNumbers1 b


--compares lambda lifted expression with original expression
--if not the same, integers asociated with all the abstractions in the lambda lifted expression are put in a list by recursive calls
--if the same, puts the integer associated with the outmost abstraction in the list
checkLamLifting :: LamExpr -> LamExpr -> [Int]
checkLamLifting (LamVar x) e = []
checkLamLifting x@(LamAbs a b) e | (x /= e) =  [a]  ++ (checkLamLifting b e)
                                 | otherwise = [a]
checkLamLifting (LamApp a b) e = (checkLamLifting a e) ++ (checkLamLifting b e)


--creates abstractions from list xs aand appends expression e to them
absCreate1 :: [Int] -> LamExpr -> LamExpr
absCreate1 [x] e = (LamAbs x (e))
absCreate1 (x:xs) e = (LamAbs x (absCreate1 xs e))


--creates applications of Lambda variables given a list of integers
appCreate1 :: [Int] -> LamExpr
appCreate1 [x] = (LamVar x)
appCreate1 (x:xs)  = (LamApp (LamVar x) (appCreate1 xs))