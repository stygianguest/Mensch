module GameLogic where

import Dict
import Either(..)

import Util(combinations, greatest)

-- Game info

dIESIZE = 6
pLAYERCNT = 4
tOKENCNT = 4
sTARTOFFSET = 2+2*tOKENCNT
bOARDSIZE = pLAYERCNT * sTARTOFFSET

-- die possibilities are [1..dIESIZE]

--------------------------------------------------------------------------------
-- Game logic
--------------------------------------------------------------------------------

type Player = Int
-- players are numbered [0..pLAYERCNT-1]
allPlayers = [0..pLAYERCNT-1]

type TokenId = Int
-- tokens are numbered [0..tOKENCNT-1]

data Token = Token Player TokenId -- owner token

allTokens = map (uncurry Token) ([0..pLAYERCNT-1] `combinations` [0..tOKENCNT-1])
playerTokens player = map (Token player) [0..tOKENCNT-1]

-- token locations relative to the owner's position such that
-- Token owner relLoc
-- * if relLoc < 0, the token has not yet entered the game
-- * if relLoc == 0,  it is at the start position of owner 
-- * if relLoc >= bOARDSIZE, it is in the home row
data Location = Location Player Int -- owner distfromstart

startLocations p = map (Location p . (*) -1) [1..tOKENCNT]

firstLocation p = Location p 0

isStartLocation : Location -> Bool
isStartLocation (Location p l) = l < 0

isHomeLocation : Location -> Bool
isHomeLocation (Location p l) = l >= bOARDSIZE

isValidLocation : Location -> Bool
isValidLocation (Location p l) = -tOKENCNT <= l && l < bOARDSIZE+tOKENCNT

isBoardLocation loc =
    not (isStartLocation loc || isHomeLocation loc)

isSameLocation : Location -> Location -> Bool
isSameLocation ((Location pa la) as a) ((Location pb lb) as b) = 
    if  | pa == pb -> la == lb
        | not (isBoardLocation a && isBoardLocation b) -> False
        | otherwise -> absLoc a == absLoc b

absLoc : Location -> Int
absLoc (Location player loc) = 
    if  | loc < 0          -> loc
        | loc >= bOARDSIZE -> loc
        | otherwise        -> (sTARTOFFSET * player + loc) `mod` bOARDSIZE

advanceLocation : Int -> Location -> Location
advanceLocation dist (Location p l) =
    let maxPosLen = bOARDSIZE+tOKENCNT - 1
        target = l+dist
        newPos = target - 2*(0 `max` (target - maxPosLen))
    in Location p newPos

-- Nothing implies distance is infinite
locationDistance : Location -> Location -> Maybe Int
locationDistance (Location pA lA as locA) (Location pB lB as locB) =
    if  | (isHomeLocation locA || isHomeLocation locB) -> Nothing
        | otherwise -> 
            Just <| absLoc (Location pA (lA `max` 0)) - absLoc (Location pB (lB `max` 0))

type GameState = 
    { currentPlayer : Player
    , die : Int
    , tokenLoc : Dict.Dict (Player,TokenId) Location
    , log : [String]
    --, trace : [InputCmd]
    , randSeed : Int
    }

initGameState : GameState
initGameState = 
    { currentPlayer = 0 
    , die = 6
    , tokenLoc = initTokenLoc -- Dict.insert (0,2) (Location 0 <| bOARDSIZE+1) initTokenLoc 
    , log = []
    --, trace = []
    , randSeed = 3571
    }

initTokenLoc : Dict.Dict (Player,TokenId) Location
initTokenLoc = 
    let mkStartLoc (Token p t) = Location p (-t - 1) -- (bOARDSIZE+3-t)
        unpackedAllTokens = [0..pLAYERCNT-1] `combinations` [0..tOKENCNT-1]
    in Dict.fromList <| zip unpackedAllTokens <| map mkStartLoc allTokens

---- functions to modify or query the gamestate

newGame : GameState -> GameState
newGame gs =
    { gs | tokenLoc <- initTokenLoc 
         , currentPlayer <- gs.randSeed `mod` pLAYERCNT
    }

getLocation : GameState -> Token -> Location
getLocation gs (Token p t) = 
    case Dict.lookup (p,t) gs.tokenLoc of
    Just loc -> loc
    -- Nothing -> --it should (tm) be impossible

setLocation : Token -> Location -> GameState -> GameState
setLocation (Token p t) loc gs = 
    { gs | tokenLoc <- Dict.insert (p,t) loc gs.tokenLoc }

lookupOccupant : GameState -> Location -> Maybe Token
lookupOccupant gs loc =
    case filter (isSameLocation loc . getLocation gs) allTokens of
    [] -> Nothing
    hd::_ -> Just hd

advanceToken : Token -> Int -> GameState -> GameState
advanceToken (Token p t as tok) dist gs =
    let newLoc = advanceLocation dist currentLoc
        currentLoc = getLocation gs tok
    in { gs | tokenLoc <- Dict.insert (p,t) newLoc gs.tokenLoc }

logMsg msg gs = { gs | log <- msg :: gs.log }
pushCmd cmd gs = { gs | trace <- cmd :: gs.trace }

returnToStart : Token -> GameState -> GameState
returnToStart ((Token p t) as tok) gs = 
    let newLoc = if isStartLocation currentLoc 
                    then currentLoc 
                    else case freeLocs of
                            hd::_ -> hd
                            [] -> Location p (-t-1)-- shouldn't happen
        currentLoc = getLocation gs tok
        occupied = filter isStartLocation <| map (getLocation gs) (playerTokens p)
        isNotOccupied loc = not <| any (isSameLocation loc) occupied
        freeLocs = filter isNotOccupied (startLocations p)
        --debugMsg = show (tok, currentLoc, occupied, freeLocs)
    in setLocation tok newLoc gs

emptyLocation : Location -> GameState -> GameState
emptyLocation loc gs =
    case lookupOccupant gs loc of
    Nothing -> gs
    Just tok -> returnToStart tok gs
          
-- poor-man's quasi random number generation
throwDice : GameState -> GameState
throwDice gs = 
    let z = 3559 * gs.die + gs.randSeed
    in { gs | die <- (z `mod` dIESIZE) + 1
            , randSeed <- z `div` dIESIZE
       }

seedRand :  Int -> GameState -> GameState
seedRand seed gs = { gs | die <- (seed `mod` dIESIZE) + 1 }

nextPlayer gs = 
    { gs | currentPlayer <- (gs.currentPlayer + 1) `mod` pLAYERCNT }
endOfTurn = throwDice . nextPlayer


playersAtHome : GameState -> [Player]
playersAtHome gs =
    filter (all (isAtHome gs) . playerTokens) allPlayers

gameOver : GameState -> Bool
gameOver = not . isEmpty . playersAtHome

----

activeTokens : GameState -> [Token]
activeTokens gs =
    filter (isBoardLocation . getLocation gs)  allTokens

getTargetLocation : GameState -> Token -> Location
getTargetLocation gs (Token owner _ as tok) =
    let currentLoc = getLocation gs tok
    in if isStartLocation currentLoc 
        then firstLocation owner
        else advanceLocation (gs.die) currentLoc


tryMove : GameState -> Token -> Either String GameState
tryMove gs (Token owner t as tok) =
    let currentLoc = getLocation gs tok
        targetLoc = getTargetLocation gs tok
        isOccupiedByOwner = 
            case lookupOccupant gs targetLoc of
            Nothing    -> False
            Just (Token p _) -> p == owner

    in if | gs.currentPlayer /= owner ->
                Left "Not token of current player"
          | isStartLocation currentLoc && gs.die /= dIESIZE ->
                Left "Can only enter a token on six"
          | isOccupiedByOwner ->
                Left "Target location already occupied by current player"
          | isStartLocation currentLoc && gs.die == dIESIZE ->
                Right 
                    <| throwDice 
                    <| setLocation tok (firstLocation owner) 
                    <| emptyLocation targetLoc gs
          | otherwise ->
                Right 
                    <| (if gs.die == dIESIZE then throwDice else endOfTurn)
                    <| advanceToken tok gs.die 
                    <| emptyLocation targetLoc gs

moveableTokens : GameState -> Int -> [Token]
moveableTokens gs player =
    filter (isRight . tryMove gs) (playerTokens player)


advanceOnBlocked : GameState -> GameState
advanceOnBlocked gs =
    case moveableTokens gs gs.currentPlayer of
    [] -> logMsg "No possible moves, passing turn" <| endOfTurn gs
    otherwise -> gs


data InputCmd = EndOfTurn | MoveToken Token | CancelMove | NoCmd

execCmd : InputCmd -> GameState -> GameState
execCmd cmd gs = 
    case cmd of
    MoveToken tok ->
        case tryMove gs tok of
        Left msg -> advanceOnBlocked <| logMsg msg gs
        Right gs' -> gs'
--    CancelMove -> undoCmd
    NoCmd -> advanceOnBlocked gs
    otherwise -> logMsg (show cmd) gs

--------------------------------------------------------------------------------
-- AI
--------------------------------------------------------------------------------

-- a strategy defines an order for different moves in a specific gamestate
-- the ``smallest'' element will be the result of the strategy
type Strategy = GameState -> Token -> Token -> Bool

-- define strategy from a boolean property such that
-- moving tokA is better than (or eq to) moving tokB 
-- iff cond holds for tokA in the given gamestate
betterToSatisfy : (GameState -> Token -> Bool) -> Strategy
betterToSatisfy cond gs tokA tokB = cond gs tokA || not (cond gs tokB)

-- combine two strategies defined by <=' and <='' to define a third <= s.t.
-- tokA <= tokB  iff  tokA <' tokB or (tokA ==' tokB and tokA <='' tokB)
-- thus the second ordering only determines the order if the first comparison
-- deems tokA and tokB equal
(>|>) : Strategy -> Strategy -> Strategy
(>|>) f g gs tokA tokB = 
    if
       | f gs tokA tokB && f gs tokB tokA -> g gs tokA tokB
       | otherwise            -> f gs tokA tokB --note that (tokA !=' tokB)

hitsOpponent : GameState -> Token -> Bool
hitsOpponent gs = isJust . lookupOccupant gs . getTargetLocation gs

canBeHit : GameState -> Token -> Bool
canBeHit gs (Token p _ as tok) = 
    let otherTokens = filter differentOwner allTokens
        differentOwner (Token p' _) = p' /= p
        tokLoc = getLocation gs tok
        tokenDistances = map (locationDistance tokLoc . getLocation gs) otherTokens
        isHittingDist dist =
            case dist of
            Nothing -> False
            Just d -> d <= dIESIZE

    in any isHittingDist tokenDistances

isAtHome : GameState -> Token -> Bool
isAtHome gs = isHomeLocation . getLocation gs

--FIXME: following should compare also if player isn't the same
isAheadOf : Strategy
isAheadOf gs tokA tokB =
    let (Location _ lA) = getLocation gs tokA
        (Location _ lB) = getLocation gs tokB
    in lA >= lB

--TODO: sort tokens by the likelyhood (number of die throws that will get it hit)
defensiveStyle = betterToSatisfy canBeHit
aggressiveStyle = betterToSatisfy hitsOpponent

eagerStrategy = betterToSatisfy (\gs -> not . isAtHome gs) >|> isAheadOf
hedgeStrategy gs tokA tokB = isAheadOf gs tokB tokA -- reverses the order

computerPlayer : Strategy -> Int -> GameState -> InputCmd
computerPlayer strategy player gs =
    let moveable = filter (isRight . tryMove gs) (playerTokens player)

        isWorseCmd x y =
            case (x,y) of
                (MoveToken tokA, MoveToken tokB) ->
                     strategy gs tokB tokA -- note reversed arguments
                (NoCmd, MoveToken _) -> True -- always better to move
                (MoveToken _, NoCmd) -> False 
                otherwise -> True

    in greatest isWorseCmd NoCmd (map MoveToken moveable)
