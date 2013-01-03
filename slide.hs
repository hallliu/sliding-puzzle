module Main where
import Data.List
import System.Random
import System.IO
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map

data Puzzle = Puzzle [Int] Int --array of Ints of length n^2
    deriving (Eq,Ord)

initPuzzle :: Int -> Puzzle
initPuzzle n = Puzzle [0..(n^2-1)] n

solvable :: [Int] -> Int -> Bool --decides if puzzle is solvable by computing parity
solvable p n
    | parityL p n == -1 = False
    | otherwise = True

parityL :: [Int] -> Int -> Int --parity of a whole grid
parityL ns size = sgn ns * mDistr 0 (fromJust $ elemIndex 0 ns) size

sgn :: [Int] -> Int --the sgn function for permutations
sgn ns = product [signum (xj-xi) | xj <- ns, xi <- ns, (fromJust $ elemIndex xj ns) > (fromJust $ elemIndex xi ns)] 

mDistr :: Int -> Int -> Int -> Int --calculates the grid metric between two points, reduced mod 2 into a multiplicative group
mDistr n pos size = case (mDist n pos size `mod` 2) of
                       0 -> 1
                       1 -> -1
                       _ -> error (show n ++ " " ++ show pos)

mDist :: Int -> Int -> Int -> Int
mDist n pos size = abs ((n `div` size) - (pos `div` size)) + abs((n `mod` size) - (pos `mod` size))

randPuzzle :: Puzzle -> StdGen -> Puzzle --generates random puzzle, then generates another if it's not solvable
randPuzzle (Puzzle p n) gen
    | solvable pCandidate n = Puzzle pCandidate n
    | otherwise = randPuzzle (Puzzle pCandidate n) gen'
    where (pCandidate,gen') = recShuffle [] p gen

--next three are similar to Lab 7, where we were shuffling cards
removeIndex :: Int -> [a] -> ([a], a)
removeIndex ind list = (begin ++ end, ctr)
    where begin = init $ take ind list 
          end = drop ind list
          ctr = last $ take ind list

removePiece :: [Int] -> StdGen -> (([Int], Int), StdGen)
removePiece p g = ((removeIndex rIndex p), g')
    where (rIndex, g') = randomR (1, length p) g

recShuffle :: [Int] -> [Int] -> StdGen -> ([Int],StdGen)
recShuffle s us g 
    | us == [] = (s,g')
    | otherwise  = recShuffle (newPiece:s) us' g'
        where ((us', newPiece), g') = removePiece us g

--here starts the solver
distToSolve :: Puzzle -> Int --assigns a score to each puzzle indicating how close it is to being solved. Sum of metric distances of each piece to its originating spot
distToSolve (Puzzle p n) = foldr ((+).(\x -> mDist x (fromJust $ ( x `elemIndex` p)) n)) 0 p

validMove :: Puzzle -> Int -> Bool --is a particular tile a valid move
validMove (Puzzle p n) mv = (zdist == n) || (zdist == 0)
    where zdist = abs (nind - zind)
          nind = fromJust $ elemIndex n p
          zind = fromJust $ elemIndex 0 p

indOfZero :: Puzzle -> Int
indOfZero (Puzzle p _) = fromJust $ elemIndex 0 p

move :: Puzzle -> Int -> Puzzle --makes one move on the puzzle
move (Puzzle p n) mv = Puzzle (swap mv 0 p) n

moveSeq :: Puzzle -> [Int] -> Puzzle --makes a sequence of moves
moveSeq p ns = foldl move p ns

swap :: Eq a => a -> a -> [a] -> [a] --swaps two elements of a list
swap n1 n2 ns = start ++ [k2] ++ mid ++ [k1] ++ end --this is a lot more complicated than in C...
    where (start, part1) = break (\x -> (x==n1) || (x==n2)) ns
          k1 = head part1
          (mid, part2) = break (\x -> (x==n1) || (x==n2)) (tail part1)
          k2 = head part2
          end = tail part2

--A* search through the graph. Wikipedia used as a reference
neighborNodes :: Puzzle -> [Puzzle] --filter neighbor indices, get the tile numbers, make the moves.
neighborNodes p = map ((move p).((!!) pl)) (filter (\x -> (x >= 0) && (x < n^2)) adjInds)
    where adjInds --troublesome stuff with sides
              | i0 `mod` n == 0 = [i0+1, i0-n, i0+n]
              | i0 `mod` n == n-1 = [i0-1, i0-n, i0+n]
              | otherwise = [i0+1, i0-1, i0-n, i0+n]
          i0 = indOfZero p
          Puzzle pl n = p

type PMap = Map Puzzle [Int] --the list has 3 elements, g, h, and f scores

cmpValues :: [Int] -> [Int] -> [Int] --intended to return the key list of PMap that has the lower f-value
cmpValues as bs 
    | last as < last bs = as
    | otherwise = as

distBetween :: Puzzle -> Puzzle -> Int --similar to the distToSolve function, but instead does the distance between any two puzzles
distBetween (Puzzle p1 n) (Puzzle p2 _) = foldl ((+).(\x -> mDist (fromJust $ (x `elemIndex` p1)) (fromJust $ (x `elemIndex` p2)) n)) 0 p1

aStar :: PMap -> PMap -> Map Puzzle Puzzle -> [Puzzle]
aStar closed open came_from 
    | distToSolve x == 0 = reconstruct_path came_from (came_from Map.! x) --send to path generation if goal is reached
    | otherwise = aStar (Map.insert x (open Map.! x) closed) nOpen nMap --recursive call with updated open/closed sets and node map
        where nOpen = newOpen open closed x
              x = findLowfValue (Map.assocs open) (head $ Map.assocs open) --simple search through the open set
              nMap = newMap (Map.difference nOpen open) came_from x

{-aStarIOform :: PMap -> PMap -> Map Puzzle Puzzle -> IO [Puzzle]
aStarIOform closed open came_from = do
    let x = findLowfValue (Map.assocs open) (head $ Map.assocs open)
    let nOpen = newOpen open closed x
    let nMap = newMap (Map.difference nOpen open) came_from x
    
    if distToSolve x == 0
        then do
            putStrLn $ show x
            return $ reconstruct_path came_from (came_from Map.! x)
        else do 
            --putStrLn $ show nMap
            aStarIOform (Map.insert x (open Map.! x) closed) nOpen nMap 
-}

newOpen :: PMap -> PMap -> Puzzle -> PMap --for each neighbor node, calculate the scores and insert into the open set depending on its goodness
newOpen oldOpen closed x = foldr (\(k,v) -> Map.insertWith cmpValues k v) (Map.delete x oldOpen) (map (\a -> populateTScores a (x, head (oldOpen Map.! x))) (filter (\a -> Map.notMember a closed) (neighborNodes x))) 

newMap :: PMap -> Map Puzzle Puzzle -> Puzzle -> Map Puzzle Puzzle --takes the difference of the new open and old open, gets the list of keys (i.e, the updated nodes), then builds a map and unions it with the old came_from.
newMap diff oldMap origElem = Map.fromList (map (\a -> (a, origElem)) (Map.keys diff)) `Map.union` oldMap

populateTScores :: Puzzle -> (Puzzle, Int) -> (Puzzle, [Int]) --calculates the tentative g,h,f scores for a node
populateTScores puz (x, g_x) = (puz, [g_x + 2, distToSolve puz, g_x + 2 + distToSolve puz]) --hopefully the compiler gets around this inefficiency

findLowfValue :: [(Puzzle, [Int])] -> (Puzzle,[Int]) -> Puzzle --used to determine which x to look at first
findLowfValue open (x, values) 
    | open == [] = x
    | otherwise = case ((values' !! 2) < (values !! 2)) of
                      True -> findLowfValue open' (x', values')
                      False -> findLowfValue open' (x, values)
    where (x', values'):open' = open

reconstruct_path :: Map Puzzle Puzzle -> Puzzle -> [Puzzle] --does what the name says
reconstruct_path came_from curNode
    | curNode `Map.member` came_from = (came_from Map.! curNode) : reconstruct_path came_from (came_from Map.! curNode) --trace back
    | otherwise = [curNode] --base case
              
toMoveSeq :: [Puzzle] -> [Int] --assuming that the argument is a valid sequence of moves, gives a list of moves in integer form
toMoveSeq (p:ps)
    | ps == [] = []
    | otherwise = moved p (head ps) : toMoveSeq ps

moved :: Puzzle -> Puzzle -> Int --gets the tile that was moved 
moved (Puzzle p1 _) (Puzzle p2 _) = (sum $ zipWith (\x y -> abs (x - y)) p1 p2) `div` 2

--formatting stuff
instance Show Puzzle where
    show (Puzzle p n) = makelines p n 0

makelines ps' n count
    | count >= n^2 = []
    | count `mod` n == 0 = "\n" ++ show p ++ mksp p ++ makelines ps n (count + 1)
    | otherwise = show p ++ mksp p ++ makelines ps n (count + 1)
        where (p:ps) = ps'
mksp p 
    | p < 10 = "  "
    | otherwise = " "

--testing code
--
main :: IO ()
main = do
    astartest

astartest :: IO ()
astartest = do
    gen <- newStdGen
    let start = randPuzzle (initPuzzle 3) gen --Puzzle [0,6,7,3,8,2,4,1,5] 3
    let initStats = [0, distToSolve start, distToSolve start]
    putStrLn (show start ++ show initStats)
    let puzseq = aStar Map.empty (Map.singleton start initStats) Map.empty
    putStrLn $ show (toMoveSeq puzseq)

fvaluetest :: IO ()
fvaluetest = do
    let p0 = initPuzzle 4
    let p1 = move p0 1
    let p2 = move p1 2
    let p3 = move p2 3
    let p4 = move p3 7
    let testassoc = [(p0, [1,1,2]),(p1, [2,2,2]),(p2,[3,3,3]),(p3,[4,4,4])]
    putStrLn $ show $ findLowfValue testassoc (head testassoc)

runtestmap :: IO ()
runtestmap = do
    let p0 = initPuzzle 4
    let p1 = move p0 1
    let p2 = move p1 2
    let p3 = move p2 3
    let p4 = move p3 7
    let testmap = Map.singleton p1 p0
    let testmap1 = Map.insert p2 p1 testmap
    let testmap2 = Map.insert p3 p2 testmap1
    let testmap3 = Map.insert p4 p3 testmap2
    --putStrLn $ show $ testmap3
    putStrLn $ show $ toMoveSeq $ reconstruct_path testmap3 p4
