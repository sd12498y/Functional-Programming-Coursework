module Assignment2 where
import Parsing
import System.IO

--Q1
data Op = Add | Sub | Div
    deriving (Eq,Show)

applyOp :: Op -> Maybe [Int] -> Maybe[Int] -> Maybe [Int]
applyOp _ _ Nothing = Nothing
applyOp _ Nothing _ = Nothing
applyOp z (Just xs) (Just ys)
    | (length xs) /= (length ys) = Nothing
    | z == Add = Just [x+y | (x,y) <- zip xs ys]
    | z == Sub = Just [x-y | (x,y) <- zip xs ys]
    | z == Div = 
        if elem 0 ys /= True then Just [x `div` y | (x,y) <- zip xs ys]
        else Nothing


data Expr
    = Bin Op Expr Expr 
    | Val [Int]
    | Var String
    deriving (Eq, Show)

type Env = [(String, [Int])]
--Q2
eval :: Env -> Expr -> Maybe [Int]
eval es (Bin op e1 e2) = applyOp op (eval es e1) (eval es e2)
eval es (Var s) = lookup s es
eval es (Val xs) = Just xs

--Q3

pList :: Parser Expr
pList = do
    token $ char '['
    i <- many integer
    is <- many pSomeInts
    token $ char ']'
    return (Val (i ++ is))
    where pSomeInts = do
            token $ char ','
            i <- integer
            return i

-- Problem 4

pExpr :: Parser Expr
pExpr = do 
    t <- pTerm
    ts <- many (do 
        char '+'
        t' <- pTerm
        return (Add, t')
        +++ do 
            char '-'
            t' <- pTerm
            return (Sub, t'))
    return $ foldl (\acc (h, x) -> Bin h acc x) t ts

pTerm :: Parser Expr
pTerm = do 
    f <- pFactor
    fs <- many (do 
                char '/'
                f' <- pFactor
                return (Div, f'))
    return $ foldl (\acc (h, x) -> Bin h acc x) f fs
            
pFactor :: Parser Expr
pFactor = do
    token $ char '('
    e <- pExpr
    token $ char ')'
    return e 
    +++ do
        l <- pList
        return l
        +++ do
            i <- identifier
            return (Var i)

-- Problem 5
runParser :: Parser a -> String -> Maybe a
runParser p s = 
    if snd (head rs) /= "" then Nothing
    else (Just (fst (head rs)))
    where rs = parse p s



-- Compilation --
data Instr = IVal [Int] | IBin Op | IVar String
  deriving (Eq, Show)

type Stack = [[Int]]
type Prog = [Instr]


-- Problem 6

check :: Expr -> Env -> Bool
check e env = and [length x == length y | (x,y) <- zip (rs) (tail (rs))] where rs = tempCheck e env

tempCheck :: Expr -> Env -> [[Int]]
tempCheck (Val is) env = [is]
tempCheck (Var x) env = case lookup x env of
    Just xs -> [xs]
    Nothing -> [[]]
tempCheck (Bin op e1 e2) env = tempCheck e1 env ++ tempCheck e2 env

-- Problem 7
compile :: Expr -> Env -> Maybe Prog
compile e env = if check e env == True then Just (tempCompile e env) else Nothing

tempCompile :: Expr -> Env -> Prog
tempCompile (Val is) env = [IVal is]
tempCompile (Var x) env = [IVar x]
tempCompile (Bin op e1 e2) env = tempCompile e2 env ++ tempCompile e1 env ++ [IBin op]


-- Problem 8

runProg :: Prog -> Env -> Maybe [Int]
runProg p env = case evalProg p env [] of
    Just rs -> Just (head rs)
    Nothing -> Nothing

evalProg :: Prog -> Env -> Stack -> Maybe Stack
evalProg [] env ss = Just ss
evalProg p env ss = case tempEval (head p) env ss of
    Just rs -> evalProg (tail p) env rs
    Nothing -> Nothing

tempEval :: Instr -> Env -> Stack -> Maybe Stack
tempEval (IVal xs) env ss = Just (xs:ss)
tempEval (IVar c) env ss =  Just (rs:ss) where (Just rs) = lookup c env
tempEval (IBin op) env ss = case applyOp op (Just x) (Just y) of
    Just rs -> Just (rs: drop 2 ss)
    Nothing -> Nothing
    where [x,y] = take 2 ss


-- REPL: Read-Eval-Print Loop --
main :: IO ()
main = do hSetBuffering stdin LineBuffering
          hSetBuffering stdout NoBuffering
          repl []

repl :: Env -> IO ()
repl env = do putStr "\n> "
              line <- getLine
              dispatch env line

quit :: IO ()
quit = return ()

loop :: String -> Env -> IO ()
loop str next = do putStrLn str
                   repl next

-- Problem 9
dispatch :: Env -> String -> IO ()
dispatch env s
    | s == "quit" = quit
    | s == "env" = do
        showEnv env
        loop "" env
    | otherwise = case parse pLetClause s of
            [((Just cs),s)] -> case runParser pExpr s of
                Just e -> case eval env e of
                    Just xs -> do
                        putStr cs
                        putStr " = "
                        loop (show xs) (putEnv env (cs,xs))
                    Nothing -> loop "Error" env
                Nothing -> case pIdent s of
                    Just y -> case lookup y env of
                        Just is -> do
                            putStr cs
                            putStr " = "
                            loop (show is) (putEnv env (y,is))
                        Nothing -> loop "Error" env
                    Nothing -> loop "Error" env
            [(Nothing, s)] -> case runParser pExpr s of
                Just e -> case eval env e of
                    Just xs -> do
                        putStr "ans = "
                        loop (show xs) env
                    Nothing -> loop "Error" env
                Nothing -> loop "Error" env

pLetClause :: Parser (Maybe String)
pLetClause = do
    token $ char 'l'
    char 'e'
    char 't'
    x <- identifier
    char '='
    return (Just x)
    +++
    return Nothing

showEnv :: Env -> IO()
showEnv [] = putStr ""
showEnv env = do
    putStr (fst (head env))
    putStr " = "
    if length env == 1 then putStr (show (snd (head env)))
    else putStrLn (show (snd (head env)))
    showEnv (tail env)

pIdent :: String -> Maybe String
pIdent s = case parse identifier s of
    [] ->  Nothing
    [(x ,r)] -> (Just x)

--if duplicate -> update the old one
putEnv :: Env -> (String, [Int]) -> Env
putEnv env (s, is) = ((deleteEnv env s)++[(s,is)])

--delete the variable from the environment if exist
deleteEnv :: Env -> String -> Env
deleteEnv env s = filter (\(x,y) -> x/= s) env

-- How many hours did you spend in this assignment?
-- Ans: around 8 to 10 hours
-- How do you think of it?
-- Ans: I like how the assignment is designed in a way such that all questions are related.
-- It is so interesting to reuse the functions that I built before.
-- Also, through this assignment I am really getting familiar with the newly learnt concepts.