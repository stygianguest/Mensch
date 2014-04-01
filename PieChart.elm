module PieChart(pieChart, pieChartForm) where
-- pie chart based on the example on the elm website


-- example use
--import Window
--main = pieChart 100 30 [(blue, 2), (red, 3), (yellow, 4), (green, 1)]
--main = uncurry collage <~ Window.dimensions ~ combine [constant <| pieChartForm 100 30 []]

--TODO: shouldn't assume white is the background color!!
--TODO: determine size of collage keeping the text in mind
pieChart : Float -> Float -> [(Color, Float)] -> Element
pieChart radius cwidth =
    let collsize = ceiling <| 2 * radius * 1.25 + 40 --margin for text
        singleton x = [x]
    in collage collsize collsize . singleton . pieChartForm radius cwidth

pieChartForm : Float -> Float -> [(Color, Float)] -> Form
pieChartForm radius cwidth slices =
    let (colors, parts) = unzip slices
        fracs = normalize parts
        offsets = scanl (+) 0 fracs
        sliceForms = zipWith3 (pieSlice radius) offsets fracs colors
        cutout = filled white (circle <| radius - cwidth)
        background = filled gray <| circle radius
    in group <| background :: concat sliceForms ++ [cutout]

pieSlice : Float -> Float -> Float -> Color -> [Form]
pieSlice radius offset angle colr = 
    let makePoint t = fromPolar (radius, degrees (360 * offset + t))
    in  [ filled colr . polygon <| (0,0) :: map makePoint[ 0 .. 360 * angle ]
        , toForm (asPercent angle)
            |> move (fromPolar (radius*1.25, turns (offset + angle/2)))
        ]

asPercent fraction =
    plainText <| show (toFloat . truncate <| fraction * 100) ++ "%"

normalize xs =
    let total = sum xs
    in  map (\x -> x/total) xs

zipWith3 f xs ys zs =
    case (xs,ys,zs) of
      (x::xs, y::ys, z::zs) -> f x y z :: zipWith3 f xs ys zs
      _ -> []
