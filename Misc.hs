module Misc where

-- count f xs = length $ filter f xs
-- count = length . filter
count :: (a -> Bool) -> [a] -> Int
count f [] = 0
count f (x:xs)
	| f x 	    = (1 + count f xs)
	| otherwise = count f xs

