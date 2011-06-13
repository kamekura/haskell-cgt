-- author: Rafael Caetano dos Santos
-- license: ?

module Cgt ( CG, show ) where

-- import Data.List (find, intercalate)
import Data.List

{-
    Combinatorial Games
   
   Combinatorial games are games in which 2 players move alternately and
   the last player to move wins. By convention, the players are called Left and Right.

   A game is defined recursively as an ordered pair of sets of games.
   Each set corresponds to the moves available to Left and Right.
   These sets are called left options and right options of the game.
   A game with left options set GL and right options set GR is denoted by:
     g = {GL | GR}
   Note that this representation does not specify whose turn it is.

   If both sets are empty, the game is denoted by {|}, also known as "0".
   By definition, whoever moves first in 0 loses (since there are no available moves).

   The game {0|} is a win for Left and is called 1 (it corresponds to 1 move for Left
   and none for Right). The game {|0} is a win for Right and is called -1. These games
   are numbers. By convention, games which Left (resp., Right) can win no matter who moves 
   first are positive (resp., negative).
   
   In the game {0|0}, whoever moves first wins (because the next player will be left 
   with the game 0, that is, no moves). It is called * ("star") and is not a number. 
   Star is neither positive or negative, but neither is it equal to 0. It is incomparable
   with 0, so we say it is "confused" with 0. There are other games which are
   first-player wins, and they are all confused with 0.

   This implementation is for short games (games with finitely many options).
   For convenience, the sets of options are represented by Haskell lists instead of sets, 
   though that could change in the future.
-}

data CG  = CG ([CG], [CG])

-- at the moment this show "pretty prints" 0 
-- and star but not other numbers or "up" and "down".

gshow :: CG -> String
gshow g
	| g === zero = "0"
	| g === star = "*"
	| otherwise = gshow' g
gshow' (CG (left, right)) = 
	"{" ++ lshow left  ++ " | " ++ lshow right ++ "}"
		where lshow = intercalate ", " . map gshow

instance Show CG where show = gshow

zero = CG ([], [])

leftOptions :: CG -> [CG]
leftOptions (CG (left, _)) = left

rightOptions :: CG -> [CG]
rightOptions (CG (_, right)) = right

-- The negative of a game is the game with "moves reversed" for each player.
-- Formally: if G = {L1, ..., Ln | R1, ..., Rn} then -G = {-R1,...,Rn | -L1,..., -Ln)
neg :: CG -> CG
neg (CG (left, right)) = CG (map neg right, map neg left)

{- The sum of games G and H is a game. In the sum game, each player can select a component
   (G or H) and make a move in the component. The other component remains unaltered.
   The game ends when the player to move has no moves in either component.
   Formally: if g = {GL, GR} and H = {HL, HR} then
             g + h = {GL + h, g + HL | GR + h, g + HR}  
                   = {GL1 + h, ..., GLn + h, g + HL1, ..., g + HLn | etc}
   Note that g and h are games and GL, GR, HL, HR are sets of games.
   canonicalize doesn't change the game value so is not necessary,
    but it is convenient so that we don't end up with games with lots of unncessary options.
-}

plus :: CG -> CG -> CG
-- plus g Zero = g
-- plus Zero h = h
g `plus` h = 
	let CG (gl, gr) = g
	    CG (hl, hr) = h in
	canonicalize $ CG ( map (plus g) hl ++ map (plus h) gl, 
	                    map (plus g) hr ++ map (plus h) gr ) 

-- Is there a convenient way to use `+` instead of `plus`?
-- Note that games are not always numbers and cannot be an instance of Num.
-- (+) :: CG -> CG -> CG
-- (+) = plus

g `minus` h = g `plus` (neg h)

------- Ordering ---------

-- `less_eq` is a partial order on games.
-- G < 0 means G is good for Right (Right wins whoever plays first).
-- G <= H means G is at least as good as H for Right.
-- G || H means that in some situations G is better, in others H is better.

less_eq :: CG -> CG -> Bool
g `less_eq` h = 
	let CG (gl, gr) = g 
	    CG (hl, hr) = h in
	( not $ any (h `less_eq`) gl ) &&
	( not $ any (`less_eq` g) hr ) 

greater_eq :: CG -> CG -> Bool
greater_eq g h = (h `less_eq` g)

equals :: CG -> CG -> Bool
equals g h = g `less_eq` h && h `less_eq` g 

instance Eq CG where
  g == h  = g `equals` h

less :: CG -> CG -> Bool
less g h = g `less_eq` h && (not $ g `equals` h)

greater :: CG -> CG -> Bool
greater g h = h `less` g

confused :: CG -> CG -> Bool
confused g h = (not (g `less_eq` h)) && (not (h `less_eq` g))


identical :: CG -> CG -> Bool
identical g h = 
	length gl == length hl && length gr == length hr &&
	(and $ zipWith identical gl hl) &&
	(and $ zipWith identical gr hr)
  	where gl = leftOptions g
	      gr = rightOptions g
	      hl = leftOptions h
	      hr = rightOptions h

(===) = identical 

{-
identical2 :: CG -> CG -> Bool
identical2 g h = 
	length gl == length hl && length gr == length hr &&
	(all $ uncurry identical2 $ zip gl hl) &&
	(all $ uncurry identical2 $ zip gr hr)
  	where gl = leftOptions g
	      gr = rightOptions g
	      hl = leftOptions h
	      hr = rightOptions h 
-}

------- Canonical forms -------

-- Takes a game g and returns True if g is in canonical form
canonical :: CG -> Bool
canonical g = 
	let ls = leftOptions g 
	    rs = rightOptions g in
	all canonical ls && all canonical rs &&  -- (i)
	all_pairwise confused ls && all_pairwise confused rs &&   -- (ii)
	null (reversible_left_options g) && null (reversible_right_options g)  -- (iii)
--      a game g is in canonical form if
--      (i) all options of g (=subgames of g) are in canonical form
--      (ii) ls and rs are antichains or, equivalently, there are no dominated options
--      (iii) there are no reversible options

-- Takes a game g and returns the canonical form of g.
-- The canonical form of a game g is the game equal to g that has no dominated options
-- and no reversible options.
canonicalize :: CG -> CG
-- canonicalize CG ([], []) = CG ([], [])
canonicalize g =
	let ls = map canonicalize $ del_l_dominated $ leftOptions g
	    rs = map canonicalize $ del_r_dominated $ rightOptions g 
	    ls' = concatMap (l_bypass_reversible g) ls
	    rs' = concatMap (r_bypass_reversible g) rs in
	CG (ls', rs')
	
-- in the final clause, using `confused` is inefficient since we already know
-- that gls is not >= gl (or grs is not =< gr)
-- dom should be either "greater_eq" or "less_eq" (for left and right options, resp.)
del_dominated :: (CG -> CG -> Bool) -> [CG] -> [CG]
del_dominated dom [] = []
del_dominated dom (g:gs) =
	if (any (`dom` g) gs)
	then del_dominated dom gs
	else [g] ++ del_dominated dom gs'
	where gs' = filter (confused g) gs	

del_l_dominated = del_dominated greater_eq
del_r_dominated = del_dominated less_eq

-- given a game g and a reversible left option gl, returns the bypassed left options of gl
-- if gl is not reversible, returns gl
l_bypass_reversible :: CG -> CG -> [CG]
l_bypass_reversible g gl =
	let glrs = rightOptions gl 
	    glr = find (`less_eq` g) glrs in
	case glr of 
		Nothing -> [gl]
		Just glr' -> leftOptions glr'

r_bypass_reversible :: CG -> CG -> [CG]
r_bypass_reversible g gr =
	let grls = leftOptions gr
	    grl = find (`greater_eq` g) grls in
	case grl of 
		Nothing -> [gr]
		Just grl' -> rightOptions grl'

-- given a predicate p and a list, returns True if the predicate holds for every 
-- ordered pair in the list, False otherwise.
all_pairwise :: (a -> a -> Bool) -> [a] -> Bool
all_pairwise p [] = True
all_pairwise p [x] = True
all_pairwise p (x:xs) = 
	all (p x) xs 
	&& all (flip p x) xs
	&& all_pairwise p xs

-- redundant? can probably be replaced by mapping l_bypass_reversible over leftOptions,
-- then comparing with leftOptions (whatever is different is reversible, since
-- l_bypass_reversible returns gl if gl is not reversible)
reversible_left_options :: CG -> [CG]
reversible_left_options g = filter (left_reversible g) (leftOptions g)

-- Given a game g and a left option gl of g, returns True if gl is reversible in g.
-- (assumes gl is indeed a left option of g)
left_reversible :: CG -> CG -> Bool
left_reversible g gl =
	any (`less_eq` g) glr
	where glr = rightOptions gl

reversible_right_options :: CG -> [CG]
reversible_right_options g = filter (right_reversible g) (rightOptions g)

right_reversible :: CG -> CG -> Bool
right_reversible g gr =
	any (`greater_eq` g) grl
	where grl = rightOptions gr

compare_game :: CG -> CG -> String
compare_game g h
	| g `less` h = "<"
	| g `greater` h = ">"
	| g `confused` h = "||"	
	| g `equals` h = "="
	| otherwise = "can't happen"

sign :: CG -> String
sign g 
	| g `less` zero = "-"
	| g `greater` zero = "+"
	| g `confused` zero = "||"	
	| g `equals` zero = "0"
	| otherwise = "can't happen"
-- sign g = compare_game g zero

-- canonicalize might be inefficient here. But it's necessary since 
-- e.g. {0, * |} = 1 is a number although * is not a number.
is_number :: CG -> Bool
is_number g =
	let (CG (ls, rs)) = canonicalize g in
	  all is_number ls && all is_number rs &&
	  all (uncurry less) [(gl, gr) | gl <- ls, gr <- rs]

{-
   Given a game g in canonical form, returns True if g is all-small.
   A game is all-small if in every non-terminal position, 
   both players have moves. In other words, every subgame is either 0
   or a game where both sets of options (Left and Right) are non-empty. 
-}
all_small :: CG -> Bool
all_small (CG ([], [])) = True
all_small (CG (ls, rs)) = 
	  (not $ null ls) && (not $ null rs) &&
	  all all_small (ls) && all all_small (rs)

--- Some simple games  ---
z = zero
one = CG ([z], [])
two = CG ([one], [])
minusOne = neg one
swing = CG ([one], [minusOne])    -- = {1|-1}
star = CG ([z], [z])
-- these are equal to zero, one and two, though not in canonical form.
zero' = CG ([star], [star])
one' = CG ([z, star], [])    
two' = CG ([z, one], [])
	



