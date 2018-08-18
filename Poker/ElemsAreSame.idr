module ElemsAreSame
import Data.Vect
--=======================================================================================================
--=======================================================================================================
--Elems are same
--=======================================================================================================
--=======================================================================================================
public export data ElemsAreSame : (xs:Vect n e) -> (ys:Vect n e) -> Type where
    ||| Empty vectors are the same
    NilIsNil :
        ElemsAreSame Nil Nil
    ||| Prepending x to two vectors with the same elements
    ||| Gives two vectors which still have the same elements
    PrependXIsPrependX :
        (x:e) -> ElemsAreSame zs zs' ->
        ElemsAreSame (x::zs) (x::zs')
    ||| Given two elements x and y
    ||| and a proof that two vectors zs and zs' have the same elements
    |||
    PrependXYIsPrependYX :
        (x:e) -> (y:e) -> ElemsAreSame zs zs' ->
        ElemsAreSame (x::(y::zs)) (y::(x::(zs')))
    -- NOTE: Probably could derive this last axiom from the prior ones
    SamenessIsTransitive :
        ElemsAreSame xs zs -> ElemsAreSame zs ys ->
        ElemsAreSame xs ys

export sameListsAreSame: (xs: Vect n e) -> ElemsAreSame xs xs
sameListsAreSame [] = NilIsNil
sameListsAreSame (x :: xs) = PrependXIsPrependX x (sameListsAreSame xs)

swap: ElemsAreSame xs ys -> ElemsAreSame ys xs
swap NilIsNil = NilIsNil
swap (PrependXIsPrependX x y) = PrependXIsPrependX x (swap y)
swap (PrependXYIsPrependYX x y z) = PrependXYIsPrependYX y x (swap z)
swap (SamenessIsTransitive x y) = SamenessIsTransitive (swap y)
                     (SamenessIsTransitive y (swap (SamenessIsTransitive x y)))

export swapHeads: ElemsAreSame (x::y::zs) us -> ElemsAreSame (y::x::zs) us
swapHeads {x} {y} {zs} {us} e = let xYIsYX = PrependXYIsPrependYX y x (sameListsAreSame zs) in
                                    SamenessIsTransitive xYIsYX e
