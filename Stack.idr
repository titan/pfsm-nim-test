module Stack

import Data.List

public export
Stack : Type -> Type
Stack a = List a

export
push : a -> Stack a -> Stack a
push e s = e :: s

export
pop : Stack a -> (Maybe a, Stack a)
pop []        = (Nothing, [])
pop (x :: xs) = (Just x, xs)

export
peek : Stack a -> Maybe a
peek = head'
