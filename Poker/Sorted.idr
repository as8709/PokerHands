module Sorted
import Data.Vect
import Card

||| Given vector of cards is sorted by value
||| in descending order
public export data Sorted: Vect n Card -> Type where
  SortEmpty :
    Sorted (the (Vect 0 Card) [])
  SortSingle:
    Sorted [x]
  SortMany:
    (x:Card) -> Sorted (y :: ys) -> (cardValue x) `GTE` (cardValue y) -> Sorted(x::y::ys)

--------------------------------------------------------------------------------
-- HeadIs, HeadIsEither

-- Proof that the specified vector has the specified head.
public export data HeadIs : Vect n e -> e -> Type where
    MkHeadIs : HeadIs (x::xs) x

-- Proof that the specified vector has one of the two specified heads.
--
-- NOTE: Could implement this as an `Either (HeadIs xs x) (HeadIs xs y)`,
--       but an explicit formulation feels cleaner.
public export data HeadIsEither : Vect n e -> (x:e) -> (y:e) -> Type where
    HeadIsLeft  : HeadIsEither (x::xs) x y
    HeadIsRight : HeadIsEither (x::xs) y x

export chooseGte: (x: Nat) -> (y:Nat) -> Either (x `GTE` y) (y `GTE` x)
chooseGte Z Z = Left LTEZero
chooseGte Z (S k) = Right LTEZero
chooseGte (S k) Z = Left LTEZero
chooseGte (S k) (S j) = case chooseGte k j of
                             (Left l) => Left (LTESucc l)
                             (Right r) => Right (LTESucc r)

export tailIsSortedToo : (p1 : Sorted (x :: xs)) -> Sorted xs
tailIsSortedToo SortSingle = SortEmpty
tailIsSortedToo (SortMany x SortSingle _) = SortSingle
tailIsSortedToo (SortMany x (SortMany y z w) _) = SortMany y z w

--=======================================================================================================
-- isSorted
--=======================================================================================================
singleNotSorted : (contra : LTE (cardValue y) (cardValue x) -> Void) -> Sorted (x :: (y :: xs)) -> Void
singleNotSorted contra (SortMany x xs p) = contra p

restNotSorted : (contra : Sorted (y :: xs) -> Void) -> Sorted (x :: (y :: xs)) -> Void
restNotSorted contra (SortMany u v p) = contra v

export isSorted: (y: Vect n Card) -> Dec (Sorted y)
isSorted [] = Yes (SortEmpty)
isSorted (x :: []) = Yes SortSingle
isSorted (x :: y :: xs) = case isLTE (cardValue y) (cardValue x) of
                            (Yes prf_single) => (case isSorted (y::xs) of
                                               (Yes prf_rest) => Yes (SortMany x prf_rest prf_single)
                                               (No contra) => No (restNotSorted contra))
                            (No contra) => No (singleNotSorted contra)
