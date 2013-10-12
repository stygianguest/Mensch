module Util where

--------------------------------------------------------------------------------
-- Generic utilility functions
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
