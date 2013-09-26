import Automaton(Automaton, run, pure)
import Graphics.Input(customButton)
import Mouse(clicks, position)
import Dict
import open Either

-- Game info

dIESIZE = 6
pLAYERCNT = 4
tOKENCNT = 4
sTARTOFFSET = 2+2*tOKENCNT
bOARDSIZE = pLAYERCNT * sTARTOFFSET

-- players are numbered [0..pLAYERCNT-1]
allPlayers = [0..pLAYERCNT-1]
-- die possibilities are [1..dIESIZE]
-- tokens are numbered [0..tOKENCNT-1]

--------------------------------------------------------------------------------
-- Game logic
--------------------------------------------------------------------------------

data Token = Token Int Int -- owner token

allTokens = map (uncurry Token) ([0..pLAYERCNT-1] `combinations` [0..tOKENCNT-1])
playerTokens player = map (Token player) [0..tOKENCNT-1]

data Location = Location Int Int -- owner distfromstart

startLocations p = map (Location p . (*) -1) [1..tOKENCNT]

firstLocation p = Location p 0

isStartLocation : Location -> Bool
isStartLocation (Location p l) = l < 0

isHomeLocation : Location -> Bool
isHomeLocation (Location p l) = l > bOARDSIZE

isValidLocation : Location -> Bool
isValidLocation (Location p l) = l < bOARDSIZE && l >= -tOKENCNT

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
advanceLocation dist (Location p l) = Location p (l+dist)

-- token locations such that
-- gs.relTokenLoc owner token = relLoc
-- where relLoc is the location of a token relative to its start position such that
-- * if relLoc < 0, the token has not yet entered the game
-- * if relLoc == 0,  it is at the start position of owner 
-- * if relLoc >= bOARDSIZE, it is in the home row

type GameState = 
    { currentPlayer : Int
    , die : Int
    , tokenLoc : Dict.Dict (Int,Int) Location
    , log : [String]
    --, trace : [InputCmd]
    , randSeed : Int
    }

initGameState : GameState
initGameState = 
    { currentPlayer = 0 
    , die = 1
    , tokenLoc = initTokenLoc
    , log = []
    --, trace = []
    , randSeed = 3
    }

initTokenLoc : Dict.Dict (Int,Int) Location
initTokenLoc = 
    let mkStartLoc (Token p t) = Location p (-t - 1)
        unpackedAllTokens = [0..pLAYERCNT-1] `combinations` [0..tOKENCNT-1]
    in Dict.fromList <| zip unpackedAllTokens <| map mkStartLoc allTokens

---- functions to modify the gamestate

getLocation : GameState -> Token -> Location
getLocation gs (Token p t) = 
    case Dict.lookup (p,t) gs.tokenLoc of
    Nothing -> head [] --it should (tm) be impossible
    Just loc -> loc

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
                    then currentLoc else head freeLocs
        currentLoc = getLocation gs tok
        occupied = filter isStartLocation <| map (getLocation gs) (playerTokens p)
        isNotOccupied loc = any (isSameLocation loc) occupied
        freeLocs = filter isNotOccupied (startLocations p)
    in setLocation tok newLoc gs

emptyLocation : Location -> GameState -> GameState
emptyLocation loc gs =
    case lookupOccupant gs loc of
    Nothing -> gs
    Just tok -> returnToStart tok gs
          
-- poor-man's quasi random number generation
throwDice : GameState -> GameState
throwDice gs = 
    let z = 7 * gs.die + gs.randSeed
    in { gs | die <- (z `mod` dIESIZE) + 1
            , randSeed <- z `div` dIESIZE
       }

nextPlayer gs = 
    { gs | currentPlayer <- (gs.currentPlayer + 1) `mod` pLAYERCNT }
endOfTurn = throwDice . nextPlayer


----

--gameOver : GameState -> Maybe Int
--gameOver gs =

activeTokens : GameState -> [Token]
activeTokens gs =
    filter (isBoardLocation . getLocation gs)  allTokens

getTargetLocation : GameState -> Token -> Location
getTargetLocation gs (Token owner _ as tok) =
    let currentLoc = getLocation gs tok
    in if isStartLocation currentLoc 
        then currentLoc 
        else firstLocation owner


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
                Left <| "Target location already occupied by current player"
          | isValidLocation targetLoc ->
                Left "Token cannot move that far"
          | isStartLocation currentLoc && gs.die == dIESIZE ->
                Right 
                    <| throwDice 
                    <| setLocation tok (firstLocation owner) 
                    <| emptyLocation targetLoc gs
          | otherwise ->
                Right 
                    <| endOfTurn 
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
    otherwise -> gs

--------------------------------------------------------------------------------
-- AI
--------------------------------------------------------------------------------

-- x is better than (or eq to) y if cond holds
cond2Cmp : (a -> Bool) -> a -> a -> Bool
cond2Cmp cond x y = cond x || not (cond y)

-- x is better than y if any of the comparisons say so
-- the order in the list is important: 
-- earlier conditions supersede later ones
stackedCmp : [a -> a -> Bool] -> a -> a -> Bool
stackedCmp conds x y =
    case conds of
    hd :: tl -> if | hd x y == hd y x -> stackedCmp tl x y
                   | hd x y           -> hd y x
    [] -> True -- without conditions all are equal

hitsOpponent : GameState -> Token -> Bool
hitsOpponent gs = isJust . lookupOccupant gs . getTargetLocation gs

isAtHome : GameState -> Token -> Bool
isAtHome gs = isHomeLocation . getLocation gs

--FIXME: following should compare also if player isn't the same
isAheadOf : GameState -> Token -> Token -> Bool
isAheadOf gs tokA tokB =
    let (Location _ lA) = getLocation gs tokA
        (Location _ lB) = getLocation gs tokB
    in lA >= lB

eagerAI : Int -> GameState -> InputCmd
eagerAI player gs =
    let moveable = filter (isRight . tryMove gs) (playerTokens player)
        --onBoard = filter (isBoardLocation gs . getLocation gs) moveable
        --atStart = filter (isStartLocation gs . getLocation gs) moveable

        isBetterMove (MoveToken tokA) (MoveToken tokB) = stackedCmp
            [ cond2Cmp (not . isAtHome gs)
            , cond2Cmp (hitsOpponent gs)
            , isAheadOf gs
            ] tokA tokB

    in greatest isBetterMove NoCmd (map MoveToken moveable)
            
            

--------------------------------------------------------------------------------
-- Board drawing
--------------------------------------------------------------------------------

pLACESIZE = 10.0
tokenForm col = group
    [ filled black (circle (pLACESIZE/1.8))
    , alpha 0.9 <| filled col (circle (pLACESIZE/1.8))
    , outlined {defaultLine | width <- 1.5} (circle (pLACESIZE/1.8))
    ]
placeForm = outlined defaultLine (circle pLACESIZE)
startPlaceForm col = group [filled col (circle pLACESIZE), placeForm]
homePlaceForm col = group [filled col (circle pLACESIZE), placeForm]

placeShadow : Color -> Form
placeShadow col = alpha 0.3 <| filled col (circle pLACESIZE)

playerColors = [red, blue, yellow, green]

boardPlaceStepSize = pLACESIZE * 3
boardDisplaySize = (2 * tOKENCNT + 4) * boardPlaceStepSize

boardPlaceStep = step boardPlaceStepSize
boardPlaceLCorner = turn (degrees -(360/pLAYERCNT))
boardPlaceRCorner = turn (degrees (360/pLAYERCNT))

boardTraj = concat <| repeatN pLAYERCNT <|
    repeatN (tOKENCNT) boardPlaceStep
    ++ boardPlaceStep . boardPlaceLCorner 
    :: repeatN (tOKENCNT-1) boardPlaceStep
    ++ boardPlaceStep . boardPlaceRCorner
    :: [boardPlaceRCorner . boardPlaceStep]

homeRowTraj = 
    boardPlaceStep . turnRight :: repeatN (tOKENCNT-1) boardPlaceStep

startPlacesTraj = 
    [ boardPlaceStep . boardPlaceStep . boardPlaceStep . turnLeft
    , turnRight . boardPlaceStep
    , turnRight . boardPlaceStep
    , boardPlaceStep
    ]

startPositions = map ((*) sTARTOFFSET) (upTo pLAYERCNT)
endPositions =
    map (\i -> (i-1+bOARDSIZE) `mod` bOARDSIZE) startPositions
boardCoords = take bOARDSIZE <| centerPath <| mkPath origin boardTraj
startCoords = map (\i-> boardCoords!!i) startPositions
endCoords = map (\i-> boardCoords!!i) endPositions
homeRowCoords = map (\s -> drop 1 <| mkPath s homeRowTraj) endCoords
startPlacesCoords =
    map (\s -> drop 1 <| mkPath s startPlacesTraj) startCoords

locationCoord : Location -> Corner
locationCoord (Location player rloc as loc) =
    if | rloc < 0 -> (startPlacesCoords !! player) !! (-rloc-1)
       | rloc >= bOARDSIZE -> (homeRowCoords !! player) !! (rloc - bOARDSIZE)
       | otherwise -> boardCoords !! absLoc loc


tokenCoord : GameState -> Token -> Corner
tokenCoord gs = locationCoord . getLocation gs

tokenCoords : GameState -> [[Corner]]
tokenCoords gs =
    map (map (tokenCoord gs) . playerTokens) allPlayers
    -- [[ tokenCoord gs tok | tok <- playerTokens p ] | p <- allPlayers ]

drawGame : GameState -> Element
drawGame gs = flow down <|
    [ collage (ceiling boardDisplaySize) (ceiling boardDisplaySize) <|
            -- color the starting places with player's color (underneath)
            zipWith drawAt (map placeShadow playerColors) startCoords 
            -- draw the all places on the board, the full circle
            ++ drawAlong placeForm boardCoords
            -- draw home row places for every player
            ++ concat (zipWith drawAlong (map homePlaceForm playerColors) homeRowCoords)
            -- draw starting places for every player
            ++ concat (zipWith drawAlong (map startPlaceForm playerColors) startPlacesCoords)
            -- draw the actual tokens
            ++ concat (zipWith drawAlong (map tokenForm playerColors) (tokenCoords gs))
            -- TODO: highlight the tokens that can move
            -- draw the die colored with the current player
            ++ [ scale 2 <| toForm <| text <| Text.color (playerColors!!gs.currentPlayer) <| toText <| show gs.die]
    ] ++ map (text . toText) gs.log

        
      

--------------------------------------------------------------------------------
-- Main / Input
--------------------------------------------------------------------------------

detectTokenClick : GameState -> (Float, Float) -> InputCmd
detectTokenClick gs click =
    let checkClick = isInsideCircle click pLACESIZE 
                     . (\c -> (c.x, c.y))
                     . tokenCoord gs
    in case filter checkClick allTokens of
        []       -> NoCmd
        tok :: _ -> MoveToken tok

isInsideCircle : (Float, Float) -> Float -> (Float, Float) -> Bool
isInsideCircle (cx,cy) r (px,py) = 
    let deltax = cx - px
        deltay = cy - py
    in deltax*deltax + deltay*deltay <= r*r

-- collage has inverted y and origin in the middle
--FIXME: should probably catch cases to prevent division by 0
collageOffset : (Int,Int)-> (Int, Int) -> (Float, Float)
collageOffset (w,h) (x,y) =
    (toFloat x - toFloat w / 2, toFloat h / 2 - toFloat y)

main =
    let click = collageOffset dim <~ sampleOn clicks position
        gameloop cpoint gs = 
            let cmds = detectTokenClick gs cpoint
                       :: map (\p -> eagerAI p gs) [1..pLAYERCNT-1]
            in foldr execCmd gs cmds
        dim = (ceiling boardDisplaySize, ceiling boardDisplaySize)
    in drawGame <~ foldp gameloop initGameState click


--------------------------------------------------------------------------------
-- Generic util
--------------------------------------------------------------------------------

isin : comparable -> [comparable] -> Bool
isin v lst = any ((==) v) lst

(!!) : [a] -> Int -> a
lst !! i = case lst of
    hd :: tl    -> if i <= 0 then hd else tl !! (i-1)
    []          -> head []

upTo : Int -> [Int]
upTo cnt = scanl (+) 0 (repeatN (cnt-1) 1)

splitAt : Int -> [a] -> ([a],[a])
splitAt cnt lst =
    if cnt > 0 then case lst of
                    [] -> ([], [])
                    hd::tl ->
                        let (before, after) = splitAt (cnt-1) tl
                        in (hd::before, after)
               else ([], lst)

--FIXME: handle backward ranges?
enumFromTo : Int -> Int -> [Int]
enumFromTo from to = scanl (+) from (repeatN (to-from) 1)

repeatN : Int -> a -> [a]
repeatN n elem = 
  if n > 0 then elem :: repeatN (n-1) elem else []

combinations : [a] -> [b] -> [(a,b)]
combinations lstA lstB =
    case lstA of
        []          -> []
        hd :: tl    -> map ((,) hd) lstB ++ combinations tl lstB

least : (a -> a -> Bool) -> a -> [a] -> a
least isLE smallest lst =
    case lst of
    [] -> smallest
    hd::tl -> let newsmallest =
                    if smallest `isLE` hd then smallest else hd
              in least isLE newsmallest tl

greatest cmp = least (\x y -> not (cmp x y))


--------------------------------------------------------------------------------
-- Draw utils
--------------------------------------------------------------------------------

drawAlong : Form -> [Corner] -> [Form]
drawAlong form path =
    map (drawAt form) path 

drawAt : Form -> Corner -> Form
drawAt form {x,y,a} = move (x,y) <| rotate -a form

mkPath : Corner -> [Corner -> Corner] -> [Corner]
mkPath start = scanl (<|) start 

pathBB path = case path of
    []     -> (0,0,0,0)
    hd::tl -> let maxX = maximum (map .x path)
                  minX = minimum (map .x path)
                  maxY = maximum (map .y path)
                  minY = minimum (map .y path)
              in (maxX, minX, maxY, minY)

--TODO: generalize to get a bounding box
-- creates path with origin at center
centerPath : [Corner] -> [Corner]
centerPath path = 
    let (maxX, minX, maxY, minY) = pathBB path
        offX = maxX - (maxX - minX) / 2.0
        offY = maxY - (maxY - minY) / 2.0
        updatePath c = { c | x <- c.x - offX
                           , y <- c.y - offY
                       }
    in map updatePath path


-- make it all above 0
positivePath : [Corner] -> [Corner]
positivePath path = 
    let (maxX, minX, maxY, minY) = pathBB path
        updatePath c = { c | x <- c.x + minX
                           , y <- c.y + minY
                       }
    in map updatePath path
    

type Corner = {x:Float, y:Float , a:Float}
origin = {x=0,y=0,a=0}

step : Float -> Corner -> Corner
step dist {x,y,a} = 
    { x = x + dist * (sin a)
    , y = y + dist * (cos a)
    , a = a
    }

turn : Float -> Corner -> Corner
turn angle {x,y,a} = {x=x, y=y, a=a+angle}

turnLeft = turn (degrees -90)
turnRight = turn (degrees 90)
