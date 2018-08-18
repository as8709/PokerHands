module InsertionSort
import Data.Vect

import Sorted
import Card
import ElemsAreSame


restLemma : (s : GTE (cardValue y) (cardValue z)) -> (r_prf : GTE (cardValue y) (cardValue x)) -> (restIsSorted : Sorted rest) -> (restHead : HeadIsEither rest x z) -> (w : Sorted (z :: ys)) -> Sorted (y :: rest)
restLemma {y} s r_prf restIsSorted HeadIsLeft w = SortMany y restIsSorted r_prf
restLemma {y} s r_prf restIsSorted HeadIsRight w = SortMany y restIsSorted s

elemsSwap : (restElems : ElemsAreSame (x :: (z :: ys)) rest) -> ElemsAreSame (x :: (y :: (z :: ys))) (y :: rest)
elemsSwap {y} restElems = swapHeads (PrependXIsPrependX y restElems)


total insert': (x: Card) -> (ys: Vect (S n) Card) -> Sorted ys -> HeadIs ys y ->  (z:Vect (S (S n)) Card **(Sorted z, ElemsAreSame (x::ys) z, HeadIsEither z x y))
insert' x (y::[]) SortSingle MkHeadIs = case chooseGte (cardValue x) (cardValue y) of
                                                  (Left l_prf) => (x::y::[] **(SortMany x SortSingle l_prf, PrependXIsPrependX x (PrependXIsPrependX y NilIsNil), HeadIsLeft))
                                                  (Right r_prf) => (y::x::[] **(SortMany y SortSingle r_prf, PrependXYIsPrependYX x y NilIsNil, HeadIsRight))
insert' x (y::(z :: ys)) (SortMany y w s) MkHeadIs = case chooseGte (cardValue x) (cardValue y) of
                                                (Left l_prf) => (x::y::z::ys ** (SortMany x (SortMany y w s) l_prf,
                                                                                 PrependXIsPrependX x (PrependXIsPrependX y (PrependXIsPrependX z (sameListsAreSame ys))),
                                                                                 HeadIsLeft))
                                                (Right r_prf) => let (rest ** (restIsSorted, restElems, restHead)) = insert' x (z::ys) (tailIsSortedToo (SortMany y w s)) MkHeadIs in
                                                                     (y::rest ** (restLemma s r_prf restIsSorted restHead w,
                                                                                  elemsSwap restElems,
                                                                                  HeadIsRight))

insert : (x: Card) -> (xs:Vect n Card) -> Sorted xs -> (z:Vect (S n) Card ** (Sorted z, ElemsAreSame (x::xs) z))
insert x [] sort_pf = ([x] ** (SortSingle, PrependXIsPrependX x NilIsNil))
insert x (y::ys) sort_pf = let (sortedList ** (sort_prf, sort_elems_prf, head_prf)) = insert' x (y::ys) sort_pf MkHeadIs in
                             (sortedList ** (sort_prf, sort_elems_prf))



export insertSort: (x:Vect n Card) -> (y:Vect n Card ** (Sorted y, ElemsAreSame x y))
insertSort [] = ([] ** (SortEmpty, NilIsNil))
insertSort (x :: []) = ([x] ** (SortSingle,(PrependXIsPrependX x NilIsNil)))
insertSort (x :: xs) = let (rest ** (sort, elem)) = insertSort xs
                           (y ** (o_sort, o_elems)) = insert x rest sort
                           elem_prf_new = PrependXIsPrependX x elem
                           o_elems_new = SamenessIsTransitive elem_prf_new o_elems
                           in
                           (y ** (o_sort, o_elems_new))
