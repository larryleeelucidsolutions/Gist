{-
  Synopsis
    Defines functions that can be used to
    manipulate sorted lists using binary sort
    algorithms.
-}
module BinarySort where

-- Accepts a sorted list and returns its pivot point.
pivot :: [a] -> Int
pivot xs = div (length xs - 1) 2

{-
  Synopsis
    Accepts a sorted list, xs, finds the element
    in the middle, x, and returns (as, x, bs) where
    as represents the elements before x, and bs
    represents the elements after x, in xs.
-}
split :: [a] -> ([a], a, [a])
split xs = let (as, (x:bs)) = splitAt (pivot xs) xs
             in (as, x, bs)

{-
  Synopsis
    Accepts three arguments, f, g, and a sorted
    list xs. Finds the element x in xs such that
    f x = True, and returns a 3-tuple (as, x, bs),
    where as represents the elements before x in xs
    and bs represents the elements after x. If x
    does not exist, this function returns (as,
    Nothing, bs) where as represents the elements
    that should come before x. g y returns true iff
    y < x.
-}
split' :: (a -> Bool) -> (a -> Bool) -> [a] -> ([a], Maybe a, [a])
split' f g xs | null xs   = ([], Nothing, [])
              | otherwise =
                let (as, x, bs) = split xs
                  in
                    if f x then (as, Just x, bs)
                           else if g x
                                  then
                                    let (as', x', bs') = split' f g bs
                                      in (as ++ (x:as'), x', bs')
                                  else
                                    let (as', x', bs') = split' f g as
                                      in (as', x', bs' ++ (x:bs))

{-
  Synopsis
    Accepts two sorted lists, xs and ys, and merges
    them into a single sorted list using f as the
    less than or equal to relation.
-}
merge :: (a -> a -> Bool) -> [a] -> [a] -> [a]
merge f xs ys | null xs = ys
              | null ys = xs
              | otherwise = let (x:xs') = xs
                                (y:ys') = ys
                              in
                                if f x y
                                  then x : (merge f xs' ys)
                                  else y : (merge f xs ys')
