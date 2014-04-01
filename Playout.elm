module Playout where

import Window
import Random
import Dict
import Mouse

import Util(..)
import PieChart(pieChartForm)

import GameLogic(..)

main =
    let noGames = 2 -- number of games to run in simulation

        clock = fps 1 -- unfortunately it's rather slow
        isRunning = toggleOnce Mouse.clicks
        gameCount = keepN (noGames+1) <| count <| keepWhen isRunning second clock

        strats = shuffle (constant strategies |> sampleOn gameCount)
        rseed = Random.range 1 dIESIZE gameCount
        winnerNo = playoff <~ (isRunning |> sampleOn rseed) ~ lift (map snd) strats ~ rseed
        
        -- don't do playoff on pageload
        playoff runs = if runs then aiPlayoff else (\s a -> -1)

        playerNames = Dict.fromList . enumerate . map fst <~ strats
        winnerName = Dict.lookup <~ winnerNo ~ playerNames
        countWinners = foldp incWinner Dict.empty winnerName
        incWinner winner =
            let inc old =
                    case old of
                    Just n -> Just (n + 1)
                    Nothing -> Just 1
            in case winner of
               Just w -> Dict.update w inc
               Nothing -> id

        coloredWinCounts = zipDict strategyColors <~ countWinners
        
        chartForm = pieChartForm 100 30 . Dict.values <~ coloredWinCounts

        progressForm p = toForm <| centered <| toText <| show p ++ "/" ++ show noGames
        
        pauseForms =
            [ outlined (solid black) <| ngon 3 50
            , move (10,-60) <| toForm <| centered <| toText "click to start"
            ] 

        pauseFormsSig = constant pauseForms |> sampleOn isRunning
        runningFormsSig = combine 
            [ chartForm |> sampleOn (isRunning `mergeClocks` gameCount)
            , progressForm <~ gameCount
            ]
        drawedForms = muc isRunning pauseForms runningFormsSig pauseFormsSig

    in uncurry collage <~ Window.dimensions ~ drawedForms

clockOf = lift (\v -> ())
mergeClocks a b = clockOf a `merge` clockOf b

strategies =
    [ ("ade", aggressiveStyle >|> defensiveStyle >|> eagerStrategy)
    , ("dae", defensiveStyle >|> aggressiveStyle >|> eagerStrategy)
    , ("adh", aggressiveStyle >|> defensiveStyle >|> hedgeStrategy)
    , ("dah", defensiveStyle >|> aggressiveStyle >|> hedgeStrategy)
    ]

strategyColors = Dict.fromList
    [ ("ade", blue)
    , ("dae", yellow)
    , ("adh", red)
    , ("dah", green)
    ]

aiPlayoff : [Strategy] -> Int -> Player
aiPlayoff strats rseed =
    let playTurn gs = execCmd (player gs.currentPlayer gs) gs
        player n = computerPlayer (fromJust <| Dict.lookup n stratDict) n
        stratDict = Dict.fromList <| enumerate strats

        playOut = applyUntil playTurn (not . isEmpty . playersAtHome)
        firstGame = seedRand rseed initGameState
    in head <| playersAtHome <| playOut firstGame
