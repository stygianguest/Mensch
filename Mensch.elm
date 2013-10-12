import Automaton(Automaton, run, pure)
import Graphics.Input(customButton)
import Mouse(clicks, position)
import Dict
import Window
import open Either
import Random

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
    let mkStartLoc (Token p t) = Location p (bOARDSIZE-2-t)--(-t - 1)
        unpackedAllTokens = [0..pLAYERCNT-1] `combinations` [0..tOKENCNT-1]
    in Dict.fromList <| zip unpackedAllTokens <| map mkStartLoc allTokens

---- functions to modify or query the gamestate

newGame : GameState -> GameState
newGame gs = { gs | tokenLoc <- initTokenLoc }

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

-- x is better than (or eq to) y if cond holds
betterToSatisfy : (a -> Bool) -> a -> a -> Bool
betterToSatisfy cond x y = cond x || not (cond y)

-- x is better than y if any of the comparisons say so
-- the order in the list is important: 
-- earlier conditions supersede later ones
stackedCmp : [a -> a -> Bool] -> a -> a -> Bool
stackedCmp conds x y =
    case conds of
    hd :: tl -> if | hd x y == hd y x -> stackedCmp tl x y
                   | otherwise        -> hd x y
    [] -> True -- without conditions all are equal

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
isAheadOf : GameState -> Token -> Token -> Bool
isAheadOf gs tokA tokB =
    let (Location _ lA) = getLocation gs tokA
        (Location _ lB) = getLocation gs tokB
    in lA >= lB


--eagerStrategy gs = stackedCmp 
--    [ betterToSatisfy (not . isAtHome gs) -- if already at home, don't bother
--    , betterToSatisfy (hitsOpponent gs)
--    , isAheadOf gs
--    ]

--TODO: sort tokens by the likelyhood (number of die throws that will get it hit)
defensiveStyle gs = betterToSatisfy (canBeHit gs)
aggressiveStyle gs = betterToSatisfy (hitsOpponent gs)

eagerStrategy gs = stackedCmp 
    [ betterToSatisfy (not . isAtHome gs) -- if already at home, don't bother
    , isAheadOf gs
    ]
hedgeStrategy gs tokA tokB = isAheadOf gs tokB tokA

computerPlayer : (GameState -> Token -> Token -> Bool) -> Int -> GameState -> InputCmd
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


eagerAI : Int -> GameState -> InputCmd
eagerAI = computerPlayer eagerStrategy

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

startPositions = map ((*) sTARTOFFSET) [0..pLAYERCNT-1]
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

-- TODO: 
--      * highlight the tokens that can move
--      * draw die in corner of current player
--      * animated moves?
drawGame : (Int, Int) -> GameState -> Element
drawGame (w,h) gs = flow down <|
    [ collage w h <|
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
            -- draw the die colored with the current player
            ++ [ scale 2 <| toForm <| text <| Text.color (playerColors!!gs.currentPlayer) <| toText <| show gs.die]
            ++ endGameBanner gs
            ++ [move (0, -boardDisplaySize / 2) <| toForm <| flow down <| map (text . toText) (take 1 gs.log)]
    ] -- ++ map (text . toText) (take 1 gs.log)

endGameBanner gs = 
    case playersAtHome gs of
    [] -> []
    winner::_ ->
        [ alpha 0.9 <| filled white <| rect 300 150
        --, traced {defaultLine | width <- 5} <| rect 250 100
        , move (0,20) <| scale 3 <| toForm <| text <| toText "Game Over"
        , move (-35,-21) <| homePlaceForm <| playerColors!!winner
        , move (pLACESIZE,-18) <| scale 2 <| toForm <| text <| toText "won" 
        , move (0,-40) <| toForm <| text <| toText "refresh to start new game"
        ]

        
      

--------------------------------------------------------------------------------
-- Main / Input
--------------------------------------------------------------------------------

localHuman : (Float, Float) -> GameState -> InputCmd
localHuman click gs =
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
collageOffset : (Int,Int)-> (Int, Int) -> (Float, Float)
collageOffset (w,h) (x,y) =
    (toFloat x - toFloat w / 2, toFloat h / 2 - toFloat y)

main =
    let click = collageOffset <~ Window.dimensions ~ sampleOn clicks position
        seed = Random.range 1 dIESIZE click
        gameloop (rand,cpoint) gs = 
            let cmd = case gs.currentPlayer of
                        0 -> localHuman cpoint gs
                        n -> eagerAI n gs
                insertRandom = case gs.currentPlayer of
                    0 -> id
                    n -> seedRand rand
                logCmd = case cmd of
                    MoveToken _ -> logMsg "moving"
                    otherwise -> id
            in insertRandom <| execCmd cmd <| logCmd gs
        game = logMsg "Click red tokens to play.\nClick anywhere to advance the AI" initGameState
    in drawGame <~ Window.dimensions ~ foldp gameloop game ((,) <~ seed ~ click)


aiPlayoff : [GameState -> InputCmd] -> Int -> Int -> [Player]
aiPlayoff players rseed noGames =
    let playTurn gs = execCmd ((players !! gs.currentPlayer) gs) gs
        playOut = applyUntil playTurn (not . isEmpty . playersAtHome)
        firstGame = seedRand rseed initGameState
    in map (head . playersAtHome) <| applyN (playOut . newGame) noGames firstGame

--------------------------------------------------------------------------------
-- Generic util
--------------------------------------------------------------------------------

applyN : (a -> a) -> Int -> a -> [a]
applyN f times init =
    case times of
    0 -> []
    n -> init :: applyN f (times - 1) (f init)


applyUntil : (a -> a) -> (a -> Bool) -> a -> a
applyUntil f cond init = if cond init then init else applyUntil f cond (f init)

(!!) : [a] -> Int -> a
lst !! i = case lst of
    hd :: tl -> if i <= 0 then hd else tl !! (i-1)

repeatN : Int -> a -> [a]
repeatN n elem = 
  if n > 0 then elem :: repeatN (n-1) elem else []

combinations : [a] -> [b] -> [(a,b)]
combinations lstA lstB =
    case lstA of
        []          -> []
        hd :: tl    -> map ((,) hd) lstB ++ combinations tl lstB

least : (a -> a -> Bool) -> a -> [a] -> a
least isLE =
    let min x y = if x `isLE` y then x else y
    in foldr min

greatest cmp = least (\x y -> cmp y x)

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
