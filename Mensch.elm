import Automaton(Automaton, run, pure)
import Graphics.Input(customButton)
import Mouse(clicks, position)
import open Either

-- Game info

dIESIZE = 6
pLAYERCNT = 4
tOKENCNT = 4
sTARTOFFSET = 2+2*tOKENCNT
bOARDSIZE = pLAYERCNT * sTARTOFFSET

startPositions = map ((*) sTARTOFFSET) (upTo pLAYERCNT)
endPositions =
    map (\i -> (i-1+bOARDSIZE) `mod` bOARDSIZE) startPositions

-- players are numbered [0,..,pLAYERCNT-1]
-- die possibilities are [1,...,dIESIZE]
-- tokens are numbered [0,...,tOKENCNT-1]

--------------------------------------------------------------------------------
-- Game logic
--------------------------------------------------------------------------------

type Token = (Int, Int)

type RelLoc = Int
type AbsLoc = Int
type Player = Int

-- token locations such that
-- gs.relTokenLoc owner token = relLoc
-- where relLoc is the location of a token relative to its start position such that
-- * if relLoc < 0, the token has not yet entered the game
-- * if relLoc == 0,  it is at the start position of owner 
-- * if relLoc >= bOARDSIZE, it is in the home row

type GameState = 
    { currentplayer : Int
    , die : Int -- FIXME: remove from gamestate?
    , relTokenLoc : Int -> Int -> Int -- player -> token -> relpos
    , log : [String]
    , trace : [InputCmd]
    , randSeed : Int
    }

startState : GameState
startState = 
    { currentplayer = 0 
    , die = 1 --randomRs (1,dIESIZE) (mkStdGen 42)
    , relTokenLoc = \owner token -> token-1 -- -token - 1
    , log = []
    , trace = []
    , randSeed = 3
    }

absTokenLoc : GameState -> Int -> Int -> Int
absTokenLoc gs p t = absLoc p (relTokenLoc gs p t)

relTokenLoc : GameState -> Int -> Int -> Int
relTokenLoc gs = gs.relTokenLoc

---- functions to modify the gamestate

-- yeah, this is bad, need to have a better way to store
modifyLoc : Int -> Int -> (Int -> Int) -> GameState -> GameState
modifyLoc p t f gs =
    let newRelLocs p' t' = if p == p' && t == t' then f (relTokenLoc gs p' t')
                                                 else relTokenLoc gs p' t'
        oldLoc = relTokenLoc gs p t
    in logMsg (show ("moved",p,t,"from",oldLoc ,"to",f oldLoc)) { gs | relTokenLoc <- newRelLocs }

logMsg msg gs = { gs | log <- msg :: gs.log }
pushCmd cmd gs = { gs | trace <- cmd :: gs.trace }

advanceToken p t s gs = modifyLoc p t ((+)s) gs

resetToken : Int -> Int -> GameState -> GameState
resetToken p t gs = 
    let newpos = if currentpos < 0 then currentpos else head freePos
        currentpos = relTokenLoc gs p t
        occupied = filter (\l-> l < 0) <| map (relTokenLoc gs p) (upTo tOKENCNT)
        freePos = filter (\k -> not <| k `isin` occupied) <| map ((*) -1) [1..tOKENCNT]
    in logMsg (show ("chose", occupied, freePos)) <| modifyLoc p t (\_ -> newpos) gs
       --logMsg (show ("chose", p,t)) gs -- <| modifyLoc p t (\_ -> newpos) gs
    --let newpos = if currentpos < 0 then currentpos else head freePos
    --    currentpos = relTokenLoc gs p t
    --    occupied = filter ((<) 0) <| map (relTokenLoc gs p) (upTo tOKENCNT)
    --    freePos = filter (\k -> k `isin` occupied) <| map ((*) -1) [1..tOKENCNT]
    --in logMsg (show ("chose", freePos)) gs -- <| modifyLoc p t (\_ -> newpos) gs

emptyPlace : Int -> GameState -> GameState
emptyPlace aloc gs =
    case occupant gs aloc of
    Nothing -> gs
    Just (p,t) ->
        resetToken p t 
            <| logMsg (show ("resetToken", p, t)) gs
          
    

-- poor-man's quasi random number generation
throwDice : GameState -> GameState
throwDice gs = 
    let z = 7 * gs.die + gs.randSeed
    in { gs | die <- (z `mod` dIESIZE) + 1
            , randSeed <- z `div` dIESIZE
       }

nextPlayer gs = { gs | currentplayer <- (gs.currentplayer + 1) `mod` pLAYERCNT }
endOfTurn = throwDice . nextPlayer

--applyIf : (a -> Bool) -> (a -> a) -> a -> a
--applyIf cond f x = if cond x then f x else x

--TODO: rerun game to turn back a move?
--undoCmd : GameState -> GameState
--undoCmd gs =
--    case gs.trace of
--    []     -> startState
--    (_,gs')::tl -> startState

----

absLoc : Int -> Int -> Int
absLoc player loc = 
    if  | loc < 0          -> loc
        | loc >= bOARDSIZE -> loc
        | otherwise        -> (sTARTOFFSET * player + loc) `mod` bOARDSIZE

relLoc : Int -> Int -> Int
relLoc player loc =
    if  | loc < 0          -> loc
        | loc >= bOARDSIZE -> loc
        | otherwise        -> (loc - sTARTOFFSET * player + bOARDSIZE) `mod` bOARDSIZE


allTokens = upTo pLAYERCNT `combinations` upTo tOKENCNT

activeTokens : GameState -> [(Int, Int)]
activeTokens gs =
    filter (\(p,t) -> relTokenLoc gs p t < bOARDSIZE) allTokens


occupant : GameState -> Int -> Maybe (Int, Int)
occupant gs aloc =
    case filter ((==) aloc . uncurry (absTokenLoc gs)) (activeTokens gs) of
    [] -> Nothing
    hd::_ -> Just hd

tryMove : GameState -> Int -> Int -> Either String GameState
tryMove gs player t =
    let rtarget = if rloc < 0 then player else rloc + gs.die
        rloc = relTokenLoc gs player t
        atarget = absLoc player rtarget
        isout = rloc < 0
        occupiedBySelf = 
            case occupant gs atarget of
            Nothing    -> False
            Just (p,_) -> p == player
    in if | gs.currentplayer /= player ->
                Left "Not token of current player"
          | isout && gs.die /= dIESIZE ->
                Left "Can only enter a token on six"
          | occupiedBySelf ->
                Left <| "Target location already occupied by current player" ++ (show (occupant gs atarget, atarget, player, t, relTokenLoc gs player t, absLoc player t))
          | rtarget >= bOARDSIZE+tOKENCNT ->
                Left "Token cannot move that far"
          | isout && gs.die == dIESIZE ->
                Right <| throwDice <| advanceToken player t -rloc <| emptyPlace atarget gs
          | otherwise ->
                Right <| endOfTurn <| advanceToken player t gs.die <| emptyPlace atarget gs

moves : GameState -> [Int]
moves gs =
    filter (\t -> isRight (tryMove gs gs.currentplayer t)) (upTo tOKENCNT)

testMove : GameState -> GameState
testMove gs =
    case moves gs of
    [] -> logMsg "No possible moves, passing turn" <| endOfTurn gs
    otherwise -> gs

----

eagerAI : Int -> GameState -> InputCmd
eagerAI player gs =
    let moveable = filter (isRight . tryMove gs player) (upTo tOKENCNT)

        isWorse tokA tokB = 
            let locA = relTokenLoc gs player tokA
                locB = relTokenLoc gs player tokB
            in if | gs.die == dIESIZE && locA < 0 -> False
                  | gs.die == dIESIZE && locB < 0 -> True
                  | locA >= bOARDSIZE -> locA <= locB
                  | otherwise -> locA >= locB

        foremost = least isWorse 0 moveable

    in if gs.currentplayer /= player 
            then NoCmd
            else MoveToken player foremost

--isAfter : (Int -> Int -> Int) -> Int -> Int -> Int -> Bool
--isAfter f player tokA tokB = 
--    let locA = f player tokA
--        locB = f player tokB
--    in locA <= locB
--    --if | locA >= bOARDSIZE -> locA <= locB
--     --     | otherwise         -> locA >= locB
------

data InputCmd = EndOfTurn | MoveToken Int Int | CancelMove | NoCmd

execCmd : InputCmd -> GameState -> GameState
execCmd cmd gs = 
    case cmd of
    MoveToken p t ->
        case tryMove gs p t of
        Left msg -> testMove <| logMsg msg gs
        Right gs' -> gs'
--    CancelMove -> undoCmd
    otherwise -> gs


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

boardCoords = take bOARDSIZE <| centerPath <| mkPath origin boardTraj
startCoords = map (\i-> boardCoords!!i) startPositions
endCoords = map (\i-> boardCoords!!i) endPositions
homeRowCoords = map (\s -> drop 1 <| mkPath s homeRowTraj) endCoords
startPlacesCoords =
    map (\s -> drop 1 <| mkPath s startPlacesTraj) startCoords


tokenCoord : (Int -> Int -> Int) -> Int -> Int -> Corner
tokenCoord relLocs player token =
    let loc = relLocs player token 
    in if  | loc < 0          -> (startPlacesCoords !! player) !! (-loc - 1)
           | loc >= bOARDSIZE -> (homeRowCoords !! player) !! (loc - bOARDSIZE)
           | otherwise        -> boardCoords !! absLoc player loc

tokenCoords : (Int -> Int -> Int) -> [[Corner]]
tokenCoords relLocs = 
    map (\f-> map (\t->f t) (upTo tOKENCNT))
    <| map (tokenCoord relLocs) (upTo pLAYERCNT)
    --or, with list comprehensions,
    --[[relLocs p t] t <- upTo tOKENCNT| p <- upTo pLAYERCNT]

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
            ++ concat (zipWith drawAlong (map tokenForm playerColors) (tokenCoords (relTokenLoc gs)))
            -- TODO: highlight the tokens that can move
            -- draw the die colored with the current player
            ++ [ scale 2 <| toForm <| text <| Text.color (playerColors!!gs.currentplayer) <| toText <| show gs.die]
    ] ++ map (text . toText) gs.log

--dieForms n =
--    case n of
        
      

--------------------------------------------------------------------------------
-- Main / Input
--------------------------------------------------------------------------------

detectTokenClick : GameState -> (Float, Float) -> InputCmd
detectTokenClick gs click =
    let checkClick = isInsideCircle click pLACESIZE . getLoc
        getLoc (p,t) = (\c -> (c.x, c.y)) <| tokenCoord (relTokenLoc gs) p t
        tokens = [0..pLAYERCNT-1] `combinations` [0..tOKENCNT-1]
    in case filter checkClick tokens of
        []         -> NoCmd
        (p,t) :: _ -> MoveToken p t

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
    in drawGame <~ foldp gameloop startState click


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
