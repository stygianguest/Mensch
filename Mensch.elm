import Graphics.Input(customButton)
import Mouse(clicks, position)
import Window
import Random

import open GameLogic
import BoardDrawing(pLACESIZE, tokenCoord, drawGame)

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


--aiPlayoff : [GameState -> InputCmd] -> Int -> Int -> [Player]
--aiPlayoff players rseed noGames =
--    let playTurn gs = execCmd ((players !! gs.currentPlayer) gs) gs
--        playOut = applyUntil playTurn (not . isEmpty . playersAtHome)
--        firstGame = seedRand rseed initGameState
--    in map (head . playersAtHome) <| applyN (playOut . newGame) noGames firstGame
