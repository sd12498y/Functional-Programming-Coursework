module Assignment_one where
import Data.List
import Prelude
--Q1
fibonacci :: Int -> Int
fibonacci 0 = 0
fibonacci 1 = 1
fibonacci n = fibonacci (n-1) + fibonacci (n-2)
--Q2
--my solution is to for each string in the input list of string(1st arg), 
-- compare it with the target string (2nd arg) by putting them into "match" function.
-- if they turn out to be match, it will format the string and put into the result list.
-- if not match, it will move on to the next string in the input list
-- it stops until we have checked all strings in the input list, i.e. it is empty
lookupName :: [String] -> String -> [String]
lookupName [] y = []
lookupName (x:xs) y | match x y == True = format x : lookupName xs y
                    | otherwise = lookupName xs y
--format turns '-' to ' ' while keeping others the same
format :: String -> String
format [] = []
format (x:xs)   | x == '-' = ' ' : format xs
                | otherwise = x : format xs

--match compares two string x,y and conclude they are match if the following two conditions are True
-- (1) if the length of x is longer than or equal to x 
-- (2) zipping them together, if for every pair (i,j) generated, i==j
match :: String -> String -> Bool
match x y = and [i==j && length x >= length y|(i,j) <- zip x y]

--Q3
--my solution is first sort the input list of integers (ascending order)
--then select the last element (largest)
-- then select the head of the list (smallest)
-- then remove those selected elements by applying tail to the sorted list, and then applying tail again to reverse of the previous result
-- wave is called recursively with the above result until the input is empty
wave :: [Int] -> [Int]
wave [] = []
wave [a] = [a]
wave xs = [(!!) (sort xs) ((length xs) -1)] ++ [head (sort xs)] ++ wave (tail(reverse(tail(sort xs))))

--Q4
-- I used isAscending to check if the input list is in ascending order by check if for every elemnt i in the list, i < i+1
-- then I check every element in the list if each of them has more than 3 occurences
isStepped :: [Int] -> Bool
isStepped xs = isAscending xs && and [count xs x >=3 | x <- xs]

count :: [Int] -> Int -> Int
count xs y = length [x | x <- xs, x==y]

isAscending :: [Int] -> Bool
isAscending xs = and [xs !! n <= xs !! (n+1)| n <- [0..y]] where y = length(xs)-2 

--Q5
-- A list is said to be a Martian list if the following two conditions are both True 
-- (1) count of 1s > count of 2s. I simply use the above defined count function to count 1s and 2s
-- (2) No two adjacent elements are the same. I make every adjacent elements in pair and check if for each pair (x,y), x is not equal to y
isMartian :: [Int] -> Bool
isMartian xs = count xs 1 > count xs 2 && and [x/=y | (x,y) <- zip xs (tail xs)]

--Q6
-- I generated two lists
-- (1) a list with only even numbers
-- (2) a list with only odd numbers
-- and then for each list, I make every adjacent element in pair and check if for each pair (x,y), y is larger or equal to x
-- Note: and [] returns True 
isTwinPaired :: [Int] -> Bool
isTwinPaired xs =  and [x<=y | (x,y) <- zip es (tail es)] && and [x<=y | (x,y) <- zip os (tail os)] 
    where es = [x | x<-xs, even x]
          os = [x|x<-xs, odd x]

--Q7
-- I recursively do the follwing steps
-- (1) Call intToColumn with the result of dividing (n-1) by 26 as input
--  if the input n is smaller or equal to 0, it will return an empty list
-- (2) concatenate with: calculate the (n-1) modulus 26 and use the result as the target position to select the correspoing letters in "Z..A"
-- e.g. intToColumn 26 
-- (26-1 div 26 = 0-> []) ++ (26-1 mod 26) -> [] ++ [A] -> "A"
-- e.g. intToColumn 51
-- (51-1 div 26 = 1 -> ((1-1 div 26 = 0->[]) ++ (1-1 mod 26 = 0 -> "Z") -> []++"Z") -> "Z") ++ 51-1 mod 26 = 24 -> "B" -> "Z" ++ "B" -> "ZB" 
intToColumn :: Int -> String
intToColumn n
    | n <= 0 = []
    | n > 0 = intToColumn ((n-1) `div` 26) ++ [(reverse ['A'..'Z']) !!((n-1) `mod` 26)]

--Q8
-- my alogorithm is a recursive algorithm that:
-- (1) check if the input string is invalid, if invliad, return -1
-- (2) check if there are any operation left, if no return the result by transforming it from string to int through strToInt function
-- (3) check the next operator and do corresponding operation, i.e. add, minus, multiply, and divide. 
-- (3) (cont'd) The corresponding operation will return a manipulated string as the input of the recusively called "calculator" function. (more details see below)
calculator :: String -> Int
calculator xs
    | xs == "invalid" = -1
    | numberOfOperation xs == 0 = strToInt xs
    | nextOperator xs == '+'  = calculator (calculate_add xs)
    | nextOperator xs == '-'  = calculator (calculate_minus xs)
    | nextOperator xs == '/' = calculator (calculate_divide xs)
    | nextOperator xs == '*' = calculator (calculate_mult xs)
    | otherwise = -1

-- The following four functions do the next mathematical operation, either +,-,/, or * and return a new string corprating the result of the operation
-- e.g. "1+2+3" -> "3+3"
-- e.g. "3-2" -> "1"
-- it will also check if the operation is valid or not. if not, it will return "invalid"
-- e.g. "3/0" -> "invalid"
calculate_add :: String -> String
calculate_add xs
    | numberOfOperation xs == 1 = show (m + n)
    | otherwise = show (m + n) ++ drop ((nextOperatorPosition newXs)) newXs
    where newXs = (drop ((position '+' xs)+1) xs) --drop everything before the leftmost operator, including itself
          m = strToInt (take (position '+' xs) xs) -- turn the substring of the left hand side of the operator to integer
          n = strToInt (drop ((position '+' xs)+1) xs) -- turn the substring of the right hand side of the operator to integer

calculate_minus :: String -> String
calculate_minus xs
    | numberOfOperation xs == 1 = show (m - n)
    | otherwise = show (m - n) ++ drop ((nextOperatorPosition newXs)) newXs
    where newXs = (drop ((position '-' xs)+1) xs)
          m = strToInt (take (position '-' xs) xs)
          n = strToInt (drop ((position '-' xs)+1) xs)

calculate_divide :: String -> String
calculate_divide xs
    | n==0 = "invalid"
    | numberOfOperation xs == 1 = show (m `div` n)
    | otherwise = show (m `div` n) ++ drop ((nextOperatorPosition newXs)) newXs
    where newXs = (drop ((position '/' xs)+1) xs)
          m = strToInt (take (position '/' xs) xs)
          n = strToInt (drop ((position '/' xs)+1) xs)
    
calculate_mult :: String -> String
calculate_mult xs
    | numberOfOperation xs == 1 = show (m * n)
    | otherwise = show (m * n) ++ drop ((nextOperatorPosition newXs)) newXs
    where newXs = (drop ((position '*' xs)+1) xs)
          m = strToInt (take (position '*' xs) xs)
          n = strToInt (drop ((position '*' xs)+1) xs)
--break--

--strToInt turns string to int
strToInt :: String -> Int
strToInt xs = evalIntList (extractIntegerfromString xs)

--evalIntList takes list of integer as input and combine the elements
--e.g. [1,2,3,4] -> 1234
evalIntList :: [Int] -> Int
evalIntList [] = 0
evalIntList xs = (head xs)*(10^(length xs-1)) + evalIntList (tail xs)

-- extractIntegerfromString takes String and puttin the consecutive integer to list
-- it stop when discovering an operator
-- e.g. " 12 +" -> [1,2]
extractIntegerfromString :: String -> [Int]
extractIntegerfromString [] = []
extractIntegerfromString xs
    | isDigit x = [charToDigit x] ++ extractIntegerfromString (tail xs)
    | isOperator x = []
    | otherwise = extractIntegerfromString (tail xs)
    where x = head xs

--charToDigit simply turns Char to Int if ther can be digit
charToDigit :: Char -> Int
charToDigit c = head [x | (x,y)<-zip[0..9] ['0'..'9'] ,c==y]

--position returns the first occurence of the position of the target character c found in the list
-- if no occurence is found, -1 will be returned
position :: Char -> [Char] -> Int
position x xs
    | length ns > 0 = head ns
    | otherwise = -1
    where ns = [y | (y,z) <- zip [0..length xs-1] xs, x==z]

--nextOperatorPosition returns the firstly occured position of the next operator. If not found, -1 will be returned
nextOperatorPosition :: String -> Int
nextOperatorPosition xs
    | length ns > 0 = head ns
    | otherwise = -1
    where ns = [y | (y,z) <- zip [0..length xs-1] xs, isOperator z]
--nextOperator takes string as input and returns the next operator
nextOperator :: String -> Char
nextOperator xs
    | nextOperatorPosition xs > 0 = (!!) xs (nextOperatorPosition xs)
    | otherwise = ' '
--isDigit simply checks if the input Char is digit or not
isDigit :: Char -> Bool
isDigit c = c `elem` ['0'..'9']

--isOperator checks if the input Char is operator
isOperator :: Char -> Bool
isOperator c = c `elem` ['+','-','/','*']

--numberOfOperation finds and returns the number of operator in the string 
numberOfOperation :: String -> Int
numberOfOperation s = length [c|c<-s, isOperator c]
