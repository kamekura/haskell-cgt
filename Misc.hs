-- Miscellaneous general functions, not specific to combinatorial games.

module Misc (count, all_pairwise, none) where

-- count f xs = length $ filter f xs
-- count = length . filter
count :: (a -> Bool) -> [a] -> Int
count f [] = 0
count f (x:xs)
	| f x 	    = (1 + count f xs)
	| otherwise = count f xs

-- given a predicate p and a list, returns True if the predicate holds for every 
-- ordered pair in the list, False otherwise.
all_pairwise :: (a -> a -> Bool) -> [a] -> Bool
all_pairwise p [] = True
all_pairwise p [x] = True
all_pairwise p (x:xs) = 
	all (p x) xs 
	&& all (flip p x) xs
	&& all_pairwise p xs

none :: (a -> Bool) -> [a] -> Bool
none p = all (not . p)

