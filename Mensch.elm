main = flow down 
    [ collage 700 700 <|
        zipWith drawAt startCoords (map placeShadow pColors)
        ++ drawAlong boardCoords place
        ++ concat (zipWith drawAlong homeRowCoords (map homePlace pColors))
        ++ concat (zipWith drawAlong startPlacesCoords (map startPlace pColors))
        ++ zipWith drawAt startCoords (map token pColors)
    , asText startPositions
    , asText endPositions
    --, asText startCoords
    ]

--test  = [markdown| sadf |]

-- Game info

dIESIZE = 6
pLAYERCNT = 4
tOKENCNT = 4
sTARTOFFSET = 2+2*tOKENCNT
bOARDSIZE = pLAYERCNT * sTARTOFFSET

startPositions = map ((*) sTARTOFFSET) (upTo pLAYERCNT)
endPositions =
    map (\i -> (i-1+bOARDSIZE) `mod` bOARDSIZE) startPositions


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
startCoords = map (\i-> boardCoords!i) startPositions
endCoords = map (\i-> boardCoords!i) endPositions
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


-- Generic util

(!) : [a] -> Int -> a
lst ! i = case lst of
    hd :: tl    -> if i <= 0 then hd else tl ! (i-1)
    []          -> head []


upTo : Int -> [Int]
upTo cnt = scanl (+) 0 (repeatN (cnt-1) 1)

--FIXME: handle backward ranges?
enumFromTo : Int -> Int -> [Int]
enumFromTo from to = scanl (+) from (repeatN (to-from) 1)

repeatN : Int -> a -> [a]
repeatN n elem = 
  if n > 0 then elem :: repeatN (n-1) elem else []

loopN : Int -> [a] -> [a]
loopN n = concat . repeatN n
