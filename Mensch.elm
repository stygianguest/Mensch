import Automaton(Automaton, run, pure)
import Graphics.Input(customButton)

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

-- token locations such that
-- gs.relLocs owner token = relLoc
-- where relLoc is the location of a token relative to its start position such that
-- * if relLoc < 0, the token has not yet entered the game
-- * if relLoc == 0,  it is at the start position of owner 
-- * if relLoc >= bOARDSIZE, it is in the home row

type GameState = 
    { player : Int -- curren player
    , die : Int -- die FIXME: remove from gamestate
    , relLocs : Int -> Int -> Int -- player -> token -> relpos
    }

startState : GameState
startState = 
    { player = 0 
    , die = 0 --randomRs (1,dIESIZE) (mkStdGen 42)
    , relLocs = \owner token -> -token - 1
    }

isOut p = p < 0
isHome p = p > bOARDSIZE
isOnBoard t = not (isOut t || isHome t)

--throw : GameState -> GameState
--throw gs = { gs | die <- tail gs.dies }

-- target only works properly for tokens that are on the board
-- because it will happily move pieces past the end and enter the board on
-- throws other than six
target : GameState -> Int -> Int
target gs t = position gs t + gs.die

positions : GameState -> [[Int]]
positions gs =
    map (\o -> map (gs.relLocs o) (upTo tOKENCNT)) (upTo pLAYERCNT)

-- projected view on token positions for given player
-- who considers his start place 0
--FIXME: is currently wrong and unused anyway
--projectTokens : (Int -> Int -> Int) -> Int -> Int -> Int -> Int
--projectTokens relLocs player owner token = 
--    let location = relLocs owner token
--        playerOffset = sTARTOFFSET * ((player + owner) `mod` pLAYERCNT)
--        relLoc = (location + playerOffset) `mod` (bOARDSIZE+tOKENCNT)
--    in if location <= 0 then location else location + relLoc

absLoc : Int -> Int -> Int
absLoc player relLoc = (sTARTOFFSET * player + relLoc) `mod` bOARDSIZE

position : GameState -> Int -> Int
position gs = gs.relLocs gs.player

update : Int -> (a->a) -> [a] -> [a]
update i f lst = 
    let (before, target :: after) = splitAt i lst
    in before ++ f target :: after

isEmpty : GameState -> Int -> Bool
isEmpty gs p = snd (occupier gs p) == -1

occupier : GameState -> Int -> (Int,Int)
occupier gs p = case filter ((==) p . snd) (boardPositions gs) of
    [] -> (-1,-1)
    [occ] -> occ
    otherwise -> head [] -- "Multiple tokens at same position?!"

hasWon : GameState -> Bool
hasWon gs = all (isHome . gs.relLocs gs.player) (upTo tOKENCNT)

-- return board from the perspective of the current player
-- i.e. a finite list ending in his homerow
boardPositions : GameState -> [(Int,Int)]
boardPositions gs = 
    let startoffset owner = sTARTOFFSET * (mod (gs.player + owner) pLAYERCNT)
        renumber owner loc = (loc + startoffset owner) `mod` (bOARDSIZE+tOKENCNT)
    in  map (\(o,p) -> (o, renumber o p)) -- renumber tokens
        <| filter (\(o,p) -> isOnBoard p || o == gs.player) -- remove tokens we cannot touch
        <| concat
        <| zipWith (zip . repeatN tOKENCNT) (upTo pLAYERCNT) -- associate tokens with owners
        <| positions gs

canEnter : GameState -> Bool
canEnter gs =
    let startpos = 1 + gs.player * sTARTOFFSET
    in hasOutToks gs && snd (occupier gs startpos) /= gs.player

hasOutToks : GameState -> Bool
hasOutToks gs = any (isOut . gs.relLocs gs.player) (upTo tOKENCNT)

canMove : GameState -> Int -> Bool
canMove gs t = 
    canEnter gs && isOut (position gs t) && gs.die == dIESIZE
    || not (canEnter gs || hasOutToks gs || gs.die == dIESIZE) 
        && not (isOut (position gs t)) 
        && target gs t <= bOARDSIZE+tOKENCNT
        && snd (occupier gs (target gs t)) /= gs.player

--move : GameState -> Int -> GameState
--move gs t
--  | hasWon gs = gs
--        { player = mod (1 + player gs) pLAYERCNT }
--  | canEnter gs && isOut (position gs t) && die gs == dIESIZE = gs
--        { player = mod (1 + player gs) pLAYERCNT
--        , dies = tail (dies gs)
--        -- gs.positions[gs.player][t] += gs.die
--        , positions = update (player gs) (update t (const 1)) (positions gs)
--        }
--  | canMove gs t = gs
--        { player = mod (1 + player gs) pLAYERCNT
--        , dies = tail (dies gs)
--        -- in an impure language with arrays (and pythony syntax) this would be
--        -- gs.positions[gs.player][t] += gs.die
--        -- gs.positions[occupier.player][occupier.token] = 0
--        , positions = update (player gs) (update t (+ die gs)) 
--            ( case occupier gs (target gs t) of
--                (-1,-1) -> positions gs
--                (p,t') -> update p (update t' (const 0)) (positions gs)
--            )
--        }
--  | otherwise = gs


-- just a rough calculation to see how quickly the chances of passing a place is
--pathProb : [Float]
--pathProb = foldr next [1,0,0,0,0] [0..bOARDSIZE]
--    where next _ lst = sum (map (/5) (take 5 lst)) : lst

--------------------------------------------------------------------------------
-- Board drawing
--------------------------------------------------------------------------------

pLACESIZE = 10.0
tokenEl col = group
    [ filled black (circle (pLACESIZE/1.8))
    , alpha 0.9 <| filled col (circle (pLACESIZE/1.8))
    , outlined {defaultLine | width <- 1.5} (circle (pLACESIZE/1.8))
    ]
placeEl = outlined defaultLine (circle pLACESIZE)
startPlaceEl col = group [filled col (circle pLACESIZE), placeEl]
homePlaceEl col = group [filled col (circle pLACESIZE), placeEl]

placeShadow : Color -> Form
placeShadow col = alpha 0.3 <| filled col (circle pLACESIZE)

playerColors = [red, blue, yellow, green]

boardPlaceStep = step (pLACESIZE * 3)
boardPlaceLCorner = turn (degrees -(360/pLAYERCNT))
boardPlaceRCorner = turn (degrees (360/pLAYERCNT))

boardTraj = loopN pLAYERCNT <|
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

boardCoords = take bOARDSIZE (mkPath origin boardTraj)
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

drawGame : (Int -> Int -> Element) -> GameState -> Element
drawGame toks gs = -- flow down []
    collage 700 700 <|
        zipWith drawAt startCoords (map placeShadow playerColors)
        ++ drawAlong boardCoords placeEl
        ++ concat (zipWith drawAlong homeRowCoords (map homePlaceEl playerColors))
        ++ concat (zipWith drawAlong startPlacesCoords (map startPlaceEl playerColors))
        ++ concat (zipWith drawAlong (tokenCoords gs.relLocs) (map tokenEl playerColors))

--------------------------------------------------------------------------------
-- Main / impure
--------------------------------------------------------------------------------

data InputCmd = EndOfTurn | MoveToken Int Int | CancelMove

execGame : GameState -> Automaton InputCmd GameState
execGame gs = pure (\i -> gs)


main = 
    let signals = snd `map` concat tokenTable
        createTokenTableRow p = createToken p `map` upTo tOKENCNT
        tokenTable = createTokenTableRow `map` upTo pLAYERCNT
        tokenLookup p t = fst <| (tokenTable!!p)!!t
    in drawGame tokenLookup <~ runState execGame startState (merges signals)

--careful this isn't side-effect free!!!
createToken : Int -> Int -> (Element, Signal InputCmd)
createToken owner token =
    let (elem, sig) = customButton buttonEl buttonEl buttonEl
        --FIXME: using collage only to 'cast' Form to Element :/
        buttonEl = collage 10 10 [tokenEl (playerColors !! owner)]
        movesig = sig `sampleOn` constant (MoveToken owner token)
    in (elem, movesig)


--test  = [markdown| sadf |]

--------------------------------------------------------------------------------
-- Generic util
--------------------------------------------------------------------------------

runState : (b -> Automaton a b) -> b -> Signal a -> Signal b
runState aut s = run (aut s) s

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

loopN : Int -> [a] -> [a]
loopN n = concat . repeatN n

--------------------------------------------------------------------------------
-- Draw utils
--------------------------------------------------------------------------------

--TODO: should accept a path, not trajectory
drawAlong : [Corner] -> Form -> [Form]
drawAlong path form =
    map (\p -> drawAt p form) path 

drawAt : Corner -> Form -> Form
drawAt {x,y,a} = move (x,y) . rotate -a

mkPath : Corner -> [Corner -> Corner] -> [Corner]
mkPath start = scanl (<|) start 

-- creates path with origin at center of boundingbox
mkCyclePath : [Corner -> Corner] -> [Corner]
mkCyclePath traj = [] -- TODO:

--mkCyclic

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
