
-- Game info

dIESIZE = 6
pLAYERCNT = 4
tOKENCNT = 4
sTARTOFFSET = 2+2*tOKENCNT
bOARDSIZE = pLAYERCNT * sTARTOFFSET

startPositions = map ((*) sTARTOFFSET) (upTo pLAYERCNT)
endPositions =
    map (\i -> (i-1+bOARDSIZE) `mod` bOARDSIZE) startPositions

-- Game logic

type GameState = 
    { player : Int 
    , die : Int
    , positions : [[Int]]
    }

startState = 
    { player = 0 
    , die = 0--randomRs (1,dIESIZE) (mkStdGen 42)
    , positions = repeatN pLAYERCNT (repeatN tOKENCNT 0)
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

position : GameState -> Int -> Int
position gs t = (gs.positions !! gs.player) !! t

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
hasWon gs = all isHome (gs.positions !! gs.player)

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
        <| gs.positions

canEnter : GameState -> Bool
canEnter gs =
    let startpos = 1 + gs.player * sTARTOFFSET
    in hasOutToks gs && snd (occupier gs startpos) /= gs.player

hasOutToks : GameState -> Bool
hasOutToks gs = any isOut (gs.positions !! gs.player)

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

-- Board drawing

pLACESIZE = 10.0
token col = group
    [ filled black (circle (pLACESIZE/1.8))
    , alpha 0.9 <| filled col (circle (pLACESIZE/1.8))
    , outlined {defaultLine | width <- 1.5} (circle (pLACESIZE/1.8))
    ]
place = outlined defaultLine (circle pLACESIZE)
startPlace col = group [filled col (circle pLACESIZE), place]
homePlace col = group [filled col (circle pLACESIZE), place]

placeShadow : Color -> Form
placeShadow col = alpha 0.3 <| filled col (circle pLACESIZE)

pColors = [red, blue, yellow, green]

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


-- Draw utils

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

-- Main

main = flow down 
    [ drawGame startState
    --, asText startCoords
    ]

drawGame : GameState -> Element
drawGame gs =
    collage 700 700 <|
        zipWith drawAt startCoords (map placeShadow pColors)
        ++ drawAlong boardCoords place
        ++ concat (zipWith drawAlong homeRowCoords (map homePlace pColors))
        ++ concat (zipWith drawAlong startPlacesCoords (map startPlace pColors))
        ++ zipWith drawAt startCoords (map token pColors)
        -- ++ zipWith drawAt startCoords (map token pColors)


--test  = [markdown| sadf |]


-- Generic util

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
