module HeatMap where

import Window
import Mouse
import Dict
import Random
import Graphics.Input(customButton)

import Util(..)
import GameLogic(..)
import BoardDrawing(..)

--TODO: plot heat map of places where a token is hit
--TODO: filter out turns where nothing happened

main = 
    let gs = aiPlayoff strategies rseed
        rseed = Random.range 1 dIESIZE <| keepWhen isRunning millisecond (fps 60)
        loading = loadingAnimation isLoading
        isLoading = (\g p -> (not . gameOver) g && p) <~ gs ~ isRunning
        heatMap = drawHeatMap <~ countSteps gs

        pauseForms =
            [ outlined (solid black) <| ngon 3 50
            , move (10,-60) <| toForm <| text <| toText "click to start"
            ] 

        pauseFormsSig = constant pauseForms |> sampleOn isRunning

        drawedForms = muc isRunning pauseForms (combine [loading,heatMap]) pauseFormsSig
                       
        isRunning = toggleOnce Mouse.clicks

    in uncurry collage <~ Window.dimensions ~ drawedForms

drawHeatMap : Dict.Dict Int Int -> Form
drawHeatMap placeCount =
    let maxStepped = toFloat . maximum <| Dict.values placeCount
        normalizedCount = Dict.map (\c -> (toFloat c) / maxStepped) placeCount

        heatPlace h = filled (heatColor (0.5 + h/2)) (circle pLACESIZE)
        heatColor intensity = hsv (pi * (1 - intensity)) 1 1
        heatMap = Dict.map heatPlace normalizedCount
    in group <|
            -- color the places with frequency count (underneath)
            map (\(loc,frm) -> drawAt frm (boardCoords !! loc)) (Dict.toList heatMap)
            -- draw the all places on the board, the full circle
            ++ drawAlong placeForm boardCoords
   
countSteps : Signal GameState -> Signal (Dict.Dict Int Int)
countSteps =
    let addCnt loc =
            if not (isBoardLocation loc)
                then id
                else Dict.update (absLoc loc) inc

        inc old =
            case old of
            Just n -> Just (n + 1)
            Nothing -> Just 1

        addCnts gs counts = foldl addCnt counts <| Dict.values gs.tokenLoc

        emptyDict = Dict.fromList <| zip [0..bOARDSIZE] (repeatN bOARDSIZE 0)

    in foldp addCnts emptyDict

aiPlayoff : [Strategy] -> Signal Int -> Signal GameState
aiPlayoff strats rseed =
    let playTurn rand mgs =
            case mgs of
            Just gs -> 
                if gameOver gs 
                    then Nothing
                    else Just <| execCmd (player gs.currentPlayer gs) <| seedRand rand gs
            Nothing -> Nothing
        player n = computerPlayer (fromJust <| Dict.lookup n stratDict) n
        stratDict = Dict.fromList <| enumerate strats
    in dropAbsent initGameState <| foldp playTurn (Just initGameState) rseed


strategies =
    [ aggressiveStyle >|> defensiveStyle >|> eagerStrategy
    , defensiveStyle >|> aggressiveStyle >|> eagerStrategy
    , aggressiveStyle >|> defensiveStyle >|> hedgeStrategy
    , defensiveStyle >|> aggressiveStyle >|> hedgeStrategy
    ]
