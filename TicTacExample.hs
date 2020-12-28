-- | A simple tic-tac player based on temporal logic rewards

import           Control.Monad.State
import qualified Data.Map.Lazy       as M
import           Data.Maybe
import           Data.Random         (sampleState, uniform)
import           System.Random
import System.IO


{-
First we define the board game.

Tic tac toe is represented as follows:

1 2 3
4 5 6
7 8 9

Each square might have already been played or not. Therefore the board is
represented as a map from integers to maybe marks.
-}

data Mark = O | X | Empty deriving (Eq, Ord, Show)

type Play = Int -- represents the squares

data Player = PO | PX deriving (Eq, Ord, Show)

data GameState a = Ongoing | Over a deriving (Eq, Ord, Show)

data TicTac =
  TicTac { board         :: M.Map Play Mark
         , currentPlayer :: Player
         } deriving (Eq, Ord, Show)

gameToString :: TicTac -> String
gameToString game =
  unlines $ map f [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
  where f l = join $ map g l
        g x = case board game M.!? x of
                Nothing    -> "Something terrible happened"
                Just X     -> " X "
                Just O     -> " O "
                Just Empty -> " _ "

emptyGame :: TicTac
emptyGame = TicTac { board         = M.fromList [(p, Empty) | p<-[1..9]]
                   , currentPlayer = PO }

-- | Puts a player mark in the board
-- PO plays with Os
-- PX plays with Xs.
-- Note that the insertion is not safe and can replace existing moves
play :: TicTac -> Play -> TicTac
play g x =
  case currentPlayer g of
    PO -> g { board = M.insert x O (board g), currentPlayer = PX }
    _  -> g { board = M.insert x X (board g), currentPlayer = PO }

getPlays :: TicTac -> [Play]
getPlays g =
  if winnerQ g PO || winnerQ g PX
  then []
  else filter (\x -> b M.!? x == Just Empty) [1..9]
  where b = board g

-- | Receives a player and a game
-- Returns true if that player has three in a row the game
winnerQ :: TicTac -> Player -> Bool
winnerQ g p
  | p == PO = (f 1 == f 2 && f 2 == f 3 && f 3 == Just O) ||
              (f 4 == f 5 && f 5 == f 6 && f 6 == Just O) ||
              (f 7 == f 8 && f 8 == f 9 && f 9 == Just O) ||
              (f 1 == f 4 && f 4 == f 7 && f 7 == Just O) ||
              (f 2 == f 5 && f 5 == f 8 && f 8 == Just O) ||
              (f 3 == f 6 && f 6 == f 9 && f 9 == Just O) ||
              (f 1 == f 5 && f 5 == f 9 && f 9 == Just O) ||
              (f 3 == f 5 && f 5 == f 7 && f 7 == Just O)
  | p == PX = (f 1 == f 2 && f 2 == f 3 && f 3 == Just X) ||
              (f 4 == f 5 && f 5 == f 6 && f 6 == Just X) ||
              (f 7 == f 8 && f 8 == f 9 && f 9 == Just X) ||
              (f 1 == f 4 && f 4 == f 7 && f 7 == Just X) ||
              (f 2 == f 5 && f 5 == f 8 && f 8 == Just X) ||
              (f 3 == f 6 && f 6 == f 9 && f 9 == Just X) ||
              (f 1 == f 5 && f 5 == f 9 && f 9 == Just X) ||
              (f 3 == f 5 && f 5 == f 7 && f 7 == Just X)
  where b = board g
        f x = b M.!? x

-- Receives a player and a game state.
-- Returns True if the player has lost the game
lostQ :: TicTac -> Player -> Bool
lostQ g PO = winnerQ g PX
lostQ g _  = winnerQ g PO

stateQ :: TicTac -> GameState String
stateQ game
  | winnerQ game PO      = Over "Player O has won the game"
  | winnerQ game PX      = Over "Player X has won the game"
  | null $ getPlays game = Over "The game is a tie"
  | otherwise            = Ongoing

-- wg = play (play (play (play (play emptyGame 1) 4) 2) 5) 3

{-
Now we make a tree for the game. Each node consists of a game state and its
children are all the possible plays from that game state
-}

data GameTree = Leaf TicTac | Node TicTac [(Play, GameTree)] deriving (Eq, Show, Ord)

-- | Receives a game state and makes the game tree until a certain depth
makeTree :: TicTac -> Int -> GameTree
makeTree g n
  | n == 0           = Leaf g
  | getPlays g == [] = Leaf g
  | otherwise        = Node g (map (\x -> (x, makeTree (play g x) (n-1))) (getPlays g))

getState :: GameTree -> TicTac
getState (Leaf g)   = g
getState (Node g _) = g

{-
Now we make the grammar to model check the tree using our logic

TLF == Temporal Logic Formula
-}
data TLF a = QueryFunction (a -> Bool)
           | Not (TLF a)
           | NX (TLF a)
           | G (TLF a)
           | F (TLF a)
           | TLF a :=>: TLF a
           | TLF a :||: TLF a
           | TLF a :&&: TLF a

-- | Input: Game state, a player, an action, a temporal logic formula and the search depths
--   Returns true if the formula holds for that player
checkAction :: TicTac -> Player -> Play -> TLF TicTac -> Int -> Bool
checkAction g p a phi n = checkTree (makeTree (play g a) n) p phi

-- | Model checks the entire game tree for a given player and a given formula
checkTree :: GameTree -> Player -> TLF TicTac -> Bool
checkTree t _ (QueryFunction f) = f (getState t)
checkTree t p (Not psi) = not $ checkTree t p psi
checkTree t p (psi1 :=>: psi2) = (not $ checkTree t p psi1) || checkTree t p psi2
checkTree t p (psi1 :||: psi2) = checkTree t p psi1 || checkTree t p psi2
checkTree t p (psi1 :&&: psi2) = checkTree t p psi1 && checkTree t p psi2
checkTree t p (NX psi) =
  case t of
    Leaf _               -> False
    Node st nxtStates -> if currentPlayer st == p
                            then any (\x -> checkTree (snd x) p psi) nxtStates
                            else all (\x -> checkTree (snd x) p psi) nxtStates
checkTree t p phi@(G psi) =
  case t of
    node@(Leaf _)               -> checkTree node p psi
    node@(Node st nxtStates) -> if currentPlayer st == p
                                   then checkTree node p psi &&
                                        any (\x -> checkTree (snd x) p phi) nxtStates
                                   else checkTree node p psi &&
                                        all (\x -> checkTree (snd x) p phi) nxtStates
checkTree t p phi@(F psi) =
  case t of
    node@(Leaf _)               -> checkTree node p psi
    node@(Node st nxtStates) -> if currentPlayer st == p
                                   then checkTree node p psi ||
                                        any (\x -> checkTree (snd x) p phi) nxtStates
                                   else checkTree node p psi ||
                                        all (\x -> checkTree (snd x) p phi) nxtStates

{-
A few tests for action selection with linear temporal logic

TEST1:
board = play (play (play emptyGame 1) 5) 7
Corresponds to the board:
O _ _
_ X _
O _ _
Clearly if X plays anything other than 4 loses at the next play
Therefore

checkAction board PX 2 (G (Not (QueryFunction $ \x -> lostQ x PX))) 1
should be false

checkAction board PX 4 (G (Not (QueryFunction $ \x -> lostQ x PX))) 3
should be true

If the player X takes action 4 it becomes impossible for both agents to win the
game if we assume both take action perfectly

board' = play board 4

checkTree (makeTree board' 4) PO (F (QueryFunction $ \x -> winnerQ x PO))
should be false

checkTree (makeTree board' 4) PX (F (QueryFunction $ \x -> winnerQ x PX))
should be false
-}

{-
Designing a few tests:

TEST 1:
Checks if we can lose within three plays
checkTree (makeTree emptyGame 2) PO (G (Not (QueryFunction $ \x -> lostQ x PO)))
The result must be true

TEST 2:
Give a player a losing board and see if it can win
board = play (play (play (play (play emptyGame 1) 5) 7) 9) 3
This is the board
O _ O
_ X _
O _ X
This is clearly impossible to win for player 2 (player with X)

checkTree (makeTree board 3) PX (G (Not (QueryFunction $ \x -> lostQ x PX)))
should be false

checkTree (makeTree board 3) PO (NX (NX (QueryFunction $ \x -> winnerQ x PO)))
should be true
-}


{-
Now we design the player. Firstly, just a test, we design a player that uses
just linear temporal logic to choose the action. Later we are going to use
rewards based in linear temporal logic to actually compute state action values
-}

data Simpleton = Simpleton { player   :: Player
                           , formulas :: [TLF TicTac]
                           , depth    :: Int
                           , gen      :: StdGen}

-- just a simple player X with search depth 2 and two simple formulas. The first
-- controls the player never losing the game and the second controls the player
-- eventually winning.
simpPX = Simpleton { player = PX
                   , formulas = [ G(Not(QueryFunction (\x -> lostQ x PX)))
                                , G(F(QueryFunction (\x -> winnerQ x PX)))
                                ]
                   , depth = 2
                   , gen = mkStdGen 1}


-- Returns a play inside the state monad
simpletonPlay :: TicTac -> State Simpleton Play
simpletonPlay game = do
  simpleton <- get
  let possiblePlays = getPlays game
      p             = player simpleton
      n             = depth simpleton
      fList         = formulas simpleton
      playScore a   = sum $ map (\x -> if checkAction game p a x n then 1 else 0) fList :: Int
      bestPlays     = maxValuesBy possiblePlays playScore
      g             = gen simpleton
      (newGen, action) = case length bestPlays of
                           0 -> undefined
                           1 -> (g, head bestPlays)
                           _ -> choice bestPlays g
  put $ simpleton { gen = newGen }
  return action

-- Here are simple functions for user play and computer against computer play

prompt :: String -> IO String
prompt text = do
  putStrLn text
  hFlush stdout
  getLine

playAgainstSimpleton :: Bool -> Int -> IO ()
playAgainstSimpleton start n
  | start = userAgainstSimpleton (simpPX { depth = n }) emptyGame
  | otherwise =
    userAgainstSimpleton newSimp game'
    where (action, newSimp) = runState (simpletonPlay (emptyGame { currentPlayer = PX }))
                                       (simpPX { depth = n })
          game' = play (emptyGame { currentPlayer = PX }) action

-- | Input: A simpleton, a board game,
-- Output:
userAgainstSimpleton :: Simpleton -> TicTac -> IO ()
userAgainstSimpleton simp game = do
  putStrLn $ gameToString game
  hFlush stdout
  action <- prompt "make your move" >>= return . read
  let game' = play game action
      (compAction, newSimp) = runState (simpletonPlay game') simp
  case stateQ game' of
    Over message -> do putStrLn $ gameToString game'
                       hFlush stdout
                       putStrLn $ message
    Ongoing      -> if action `elem` getPlays game
                    then do
                           let game'' = play game' compAction
                           case stateQ game'' of
                             Over message -> do putStrLn $ gameToString game''
                                                hFlush stdout
                                                putStrLn message
                             Ongoing      ->  userAgainstSimpleton newSimp game''
                    else userAgainstSimpleton simp game

-- Here are simple util funciton
choice :: [a] -> StdGen -> (StdGen, a)
choice l g = (newGen, l!!index)
  where (index, newGen) = sampleState (uniform 0 (-1 + length l)) g

-- | Chooses a random element from a listutil functions
maxValuesBy :: (Ord b) => [a] -> (a -> b) -> [a]
maxValuesBy [] _ = undefined
maxValuesBy (x:xs) f =
  go [x] xs
  where go l [] = l
        go [] _ = undefined
        go l@(y:_) (a:xa)
          | f y < f a  = go [a] xs
          | f y == f a = go (a:l) xa
          | otherwise  = go l xa


main :: IO ()
main = undefined
