module BoardDrawing where

import GameLogic(..)
import Util((!!), repeatN)

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
            -- ++ [move (0, -boardDisplaySize / 2) <| toForm <| flow down <| map (text . toText) (take 1 gs.log)]
    ] -- ++ map (text . toText) (take 1 gs.log)

text = centered

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
