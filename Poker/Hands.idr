module Hands
import Data.Vect

import InsertionSort
import Card
import ElemsAreSame
import Sorted
import SlideWise

public export HAND_SIZE : Nat
HAND_SIZE = 5


--=======================================================================================================
--=======================================================================================================
--Utility proof data structures
--=======================================================================================================
--=======================================================================================================
data ForAll : Vect n elem -> (elem -> Type) -> Type where
  ForVect : prf x -> ForAll xs prf -> ForAll (x::r) prf
  End : ForAll [] pred

data AllSame : Vect n elem -> (elem -> elem -> Type) -> Type where
  EmptyIsSame: AllSame [] prf
  SingleIsSame: AllSame [x] prf
  Same: prf x y -> AllSame (y::ys) prf -> AllSame (x::y::ys) prf

data SameValue: Card -> Card -> Type where
  ValueMatch: SameValue (MkCard v _) (MkCard v _)

data SameSuit: Card -> Card -> Type where
  SuitMatch: SameSuit (MkCard _ s) (MkCard _ s)

--=======================================================================================================
--=======================================================================================================
--Hand Proof data structures
--=======================================================================================================
--=======================================================================================================
data PairH: Vect 2 Card -> Type where
  MkPair: PairH [(MkCard v _), (MkCard v _)]

data TwoPair: Vect HAND_SIZE Card -> Type where
  MkTwoPair: Sorted hand -> (firstpair: SlideWise2 hand PairH) -> (secondPair:SlideWise2 (getRest2 hand firstpair) PairH) -> TwoPair hand

data ThreeOfAKind : Vect 3 Card -> Type where
  MkThree: AllSame x SameValue -> ThreeOfAKind x

data Straight: Vect HAND_SIZE Card -> Type where
  MkStraight: Sorted x -> Consecutive x -> Straight x

data Flush: Vect HAND_SIZE Card -> Type where
  MkFlush: AllSame x SameSuit -> Flush x

data FullHouse: (hand:Vect HAND_SIZE Card) -> Type where
  MkFullHouse: Sorted hand -> (three: SlideWise3 hand ThreeOfAKind) -> (pair: PairH (getRest3 hand three)) -> FullHouse hand

data FourOfAKind : Vect 4 Card -> Type where
  MkFour: AllSame x SameValue -> FourOfAKind x

data StraightFlush: Vect HAND_SIZE Card -> Type where
  MkStraightFlush: Straight x -> Flush x -> StraightFlush x

--=======================================================================================================
--=======================================================================================================
--Hand
--=======================================================================================================
--=======================================================================================================
export data Hand: Vect HAND_SIZE Card -> Type where
  StraightFlushHand:
    StraightFlush x -> Hand x
  FourOfAKindHand:
    {auto p:Sorted y} -> SlideWise4 y FourOfAKind -> Hand y
  FullHouseHand:
    FullHouse y -> Hand y
  FlushHand:
    Flush x -> Hand x
  StraightHand:
    Straight x -> Hand x
  ThreeOfAKindHand:
    {auto p:Sorted y} -> SlideWise3 y ThreeOfAKind -> Hand y
  TwoPairHand:
    {auto p:Sorted y} -> TwoPair y -> Hand y
  PairHand:
    {auto p:Sorted y} -> SlideWise2 y PairH -> Hand y
  HighCardHand:
    {auto p:Sorted kickers} -> (kickers: Vect HAND_SIZE Card) -> Hand kickers

--=======================================================================================================
--=======================================================================================================
-- Utility proofs
--=======================================================================================================
--=======================================================================================================
--=======================================================================================================
-- hasSameSuit
--=======================================================================================================
notSameSuit : (contra : (s1 = s2) -> Void) -> SameSuit (MkCard value s1) (MkCard value1 s2) -> Void
notSameSuit contra SuitMatch = contra Refl

hasSameSuit: (c1: Card) -> (c2: Card) -> Dec (SameSuit c1 c2)
hasSameSuit (MkCard _ s1) (MkCard _ s2) = case decEq s1 s2 of
                                               (Yes prf) => Yes (rewrite prf in SuitMatch)
                                               (No contra) => No (notSameSuit contra)

--=======================================================================================================
-- hasSameValue
--=======================================================================================================
notSameValue : (contra : (v1 = v2) -> Void) -> SameValue (MkCard v1 suit) (MkCard v2 suit1) -> Void
notSameValue contra ValueMatch = contra Refl

hasSameValue: (c1: Card) -> (c2: Card) -> Dec (SameValue c1 c2)
hasSameValue (MkCard v1 _) (MkCard v2 _) = case decEq v1 v2 of
                                                (Yes prf) => Yes (rewrite prf in ValueMatch)
                                                (No contra) => No (notSameValue contra)
--=======================================================================================================
-- allSameSuit
--=======================================================================================================
restNotSameSuit : (contra : AllSame (x2 :: xs) SameSuit -> Void) -> AllSame (x1 :: (x2 :: xs)) SameSuit -> Void
restNotSameSuit contra (Same x y) = contra y

singleNotSameSuit : (contra : SameSuit x1 x2 -> Void) -> AllSame (x1 :: (x2 :: xs)) SameSuit -> Void
singleNotSameSuit contra (Same x y) = contra x

allSameSuit: (x: Vect n Card) -> Dec (AllSame x SameSuit)
allSameSuit [] = Yes EmptyIsSame
allSameSuit [x] = Yes SingleIsSame
allSameSuit (x1 :: x2 :: xs) = case allSameSuit (x2 :: xs) of
                                    (Yes prf_rest) => case hasSameSuit x1 x2 of
                                                               (Yes prf_single) => Yes (Same prf_single prf_rest)
                                                               (No contra) => No (singleNotSameSuit contra)
                                    (No contra) => No (restNotSameSuit contra)

--=======================================================================================================
-- isNoOfKind
--=======================================================================================================
restNotSame: (contra : AllSame (x2 :: xs) SameValue -> Void) -> AllSame (x1 :: (x2 :: xs)) SameValue -> Void
restNotSame contra (Same x y) = contra y

singleNotSame : (contra : SameValue x1 x2 -> Void) -> AllSame (x1 :: (x2 :: xs)) SameValue -> Void
singleNotSame contra (Same x y) = contra x

isNoOfKind: (x: Vect n Card) -> Dec (AllSame x SameValue)
isNoOfKind [] = Yes EmptyIsSame
isNoOfKind [x] = Yes SingleIsSame
isNoOfKind (x1 :: x2 :: xs) = case isNoOfKind (x2 :: xs) of
                           (Yes prf_rest) => (case hasSameValue x1 x2 of
                                              (Yes prf_single) => Yes (Same prf_single prf_rest)
                                              (No contra) => No (singleNotSame contra))
                           (No contra) => No (restNotSame contra)


--=======================================================================================================
--=======================================================================================================
--Hand Proofs
--=======================================================================================================
--=======================================================================================================
--=======================================================================================================
-- Pair
--=======================================================================================================
isNotPair : (contra : (v1 = v2) -> Void) -> PairH [(MkCard v1 suit), (MkCard v2 suit1)] -> Void
isNotPair contra MkPair = contra Refl

isPair: (p: Vect 2 Card) -> Dec (PairH p)
isPair [(MkCard v1 _), (MkCard v2 _)] = case decEq v1 v2 of
                                          (Yes prf) => Yes (rewrite prf in MkPair)
                                          (No contra) => No (isNotPair contra)

isPairHand: (hand: Vect HAND_SIZE Card) -> {auto sort_prf: Sorted hand }-> Dec (SlideWise2 hand PairH)
isPairHand hand {sort_prf} = isSlideWise2 hand isPair
--=======================================================================================================
-- Two Pair
--=======================================================================================================
pairInRest: {hand: Vect HAND_SIZE Card} -> (firstPair: SlideWise2 hand PairH) -> Dec (SlideWise2 (getRest2 hand firstPair) PairH)
pairInRest (HeadMatches2 searched match rest x) = isSlideWise2 (getRest2 (match ++ rest) (HeadMatches2 searched match rest x)) isPair
pairInRest (RestMatches2 x rest y) = isSlideWise2 (getRest2 (x :: rest) (RestMatches2 x rest y)) isPair


||| TODO return Dec instead
isTwoPairHand: (hand: Vect HAND_SIZE Card) -> {auto sort_prf: Sorted hand} ->  Maybe (TwoPair hand)
isTwoPairHand hand {sort_prf} = case isPairHand hand of
                                   (Yes first_prf) => (case pairInRest first_prf of
                                                      (Yes snd_prf) => Just (MkTwoPair sort_prf first_prf snd_prf)
                                                      (No contra) => Nothing)
                                   (No contra) => Nothing

--=======================================================================================================
-- Three of a Kind
--=======================================================================================================
notThreeOfAKind : (contra : AllSame x SameValue -> Void) -> ThreeOfAKind x -> Void
notThreeOfAKind contra (MkThree x) = contra x

isThreeOfAKind: (x: Vect 3 Card) -> Dec (ThreeOfAKind x)
isThreeOfAKind x = case isNoOfKind x of
                        (Yes prf) => Yes (MkThree prf)
                        (No contra) => No (notThreeOfAKind contra)

isThreeOfAKindHand: (hand: Vect 5 Card) -> {auto sort_prf: Sorted hand} -> Dec (SlideWise3 hand ThreeOfAKind)
isThreeOfAKindHand hand = isSlideWise3 hand isThreeOfAKind
--=======================================================================================================
-- Straight
--=======================================================================================================
notConsecSoNotStraight : (contra : Consecutive x -> Void) -> Straight x -> Void
notConsecSoNotStraight contra (MkStraight x y) = contra y

isStraight: (x: Vect HAND_SIZE Card) -> {auto sort_prf:Sorted x} -> Dec (Straight x)
isStraight {sort_prf} x = case isConsecutive x of
                         (Yes prf) => Yes (MkStraight sort_prf prf)
                         (No contra) => No (notConsecSoNotStraight contra)

--=======================================================================================================
-- Flush
--=======================================================================================================
notFlush : (contra : AllSame x SameSuit -> Void) -> Flush x -> Void
notFlush contra (MkFlush (Same z w)) = contra (Same z w)


isFlush: (x: Vect HAND_SIZE Card) -> Dec (Flush x)
isFlush x = case allSameSuit x of
                 (Yes prf) => Yes (MkFlush prf)
                 (No contra) => No (notFlush contra)
--=======================================================================================================
-- Full House
--=======================================================================================================
isFullHouse: (hand: Vect HAND_SIZE Card) -> (sort_prf: Sorted hand) -> Maybe (FullHouse hand)
isFullHouse hand sort_prf = case isThreeOfAKindHand hand of
                                 (No contra) => Nothing
                                 (Yes three_prf) => (case isPair (getRest3 hand three_prf) of
                                                          (Yes pair_prf) => Just (MkFullHouse sort_prf three_prf pair_prf)
                                                          (No contra) => Nothing)



--=======================================================================================================
-- Four of a Kind
--=======================================================================================================
notFourOfAKind : (contra : AllSame x SameValue -> Void) -> FourOfAKind x -> Void
notFourOfAKind contra (MkFour x) = contra x

isFourOfAKind: (x: Vect 4 Card) -> Dec (FourOfAKind x)
isFourOfAKind x = case isNoOfKind x of
                       (Yes prf) => Yes (MkFour prf)
                       (No contra) => No (notFourOfAKind contra)


isFourOfAKindHand: (hand: Vect 5 Card) -> Sorted hand -> Dec (SlideWise4 hand FourOfAKind)
isFourOfAKindHand hand sort_prf = isSlideWise4 hand isFourOfAKind

--=======================================================================================================
-- Straight Flush
--=======================================================================================================
notStraightSoNotSF : (contra : Straight x -> Void) -> StraightFlush x -> Void
notStraightSoNotSF contra (MkStraightFlush straight flush) = contra straight

notFlushSoNotSF : (contra : Flush x -> Void) -> StraightFlush x -> Void
notFlushSoNotSF contra (MkStraightFlush straight flush) = contra flush

isStraightFlush: (x: Vect HAND_SIZE Card) -> {auto sort_prf:Sorted x} -> Dec (StraightFlush x)
isStraightFlush x = case isStraight x of
                         (Yes straight_prf) => (case isFlush x of
                                            (Yes flush_prf) => Yes (MkStraightFlush straight_prf flush_prf)
                                            (No contra) => No (notFlushSoNotSF contra))
                         (No contra) => No (notStraightSoNotSF contra)


--=======================================================================================================
--=======================================================================================================
-- Hand evaluator
--=======================================================================================================
--=======================================================================================================

evalRestHand : (hand: Vect HAND_SIZE Card) -> (sort_prf : Sorted hand) -> (contra_4 : SlideWise4 hand FourOfAKind -> Void) -> (contra_sf : StraightFlush hand -> Void) -> Hand hand
evalRestHand hand sort_prf contra_4 contra_sf = case isFlush hand of
                                                     (Yes prf) => FlushHand prf
                                                     (No contra_flush) => (case isStraight hand of
                                                                                (Yes prf) => StraightHand prf
                                                                                (No contra) => (case isThreeOfAKindHand hand of
                                                                                                     (Yes prf) => ThreeOfAKindHand prf
                                                                                                     (No contra) => (case isTwoPairHand  hand of
                                                                                                                          (Just prf) => TwoPairHand prf
                                                                                                                          Nothing => (case isPairHand hand of
                                                                                                                                           (Yes prf) => PairHand prf
                                                                                                                                           (No contra) => HighCardHand hand))))


export evalHand: (hand: Vect HAND_SIZE Card) -> Sorted hand -> Hand hand
evalHand hand sort_prf = case isStraightFlush hand of
                              (Yes prf) => StraightFlushHand prf
                              (No contra_sf) => (case isFourOfAKindHand hand sort_prf of
                                                Yes prf => FourOfAKindHand prf
                                                No contra_4 => (case isFullHouse hand sort_prf of
                                                                      Just prf => FullHouseHand prf
                                                                      Nothing => evalRestHand hand sort_prf contra_4 contra_sf))



compareStraightFlushes : (x : StraightFlush h1) -> (y : StraightFlush h2) -> Ordering
compareStraightFlushes {h1 = (x1 :: xs1)} {h2 = (x2:: xs2)} x y = compare (cardValue x1) (cardValue x2)

compareFourOfAKinds : (x : SlideWise4 h1 FourOfAKind) -> (y : SlideWise4 h2 FourOfAKind) -> Ordering
compareFourOfAKinds {h1} {h2} x y = let ((x1::xs), kicker1::[]) = getMatchAndRest4 h1 x
                                        ((y1::ys), kicker2::[]) = getMatchAndRest4 h2 y in
                                        (case compare (cardValue x1) (cardValue y1) of
                                              LT => LT
                                              EQ => compare (cardValue kicker1) (cardValue kicker2)
                                              GT => GT)

compareHighCards : (h1 : Vect n Card) -> (h2 : Vect n Card) -> Ordering
compareHighCards [] [] = EQ
compareHighCards (x :: xs) (y :: ys) = case compare (cardValue x) (cardValue y) of
                                            LT => LT
                                            EQ => compareHighCards xs ys
                                            GT => GT

compareFlushes : (x : Flush h1) -> (y : Flush h2) -> Ordering
compareFlushes {h1} {h2} x y = compareHighCards h1 h2

comparePairs : {h1, h2: Vect (S(S n)) Card} -> (x : SlideWise2 h1 PairH) -> (y : SlideWise2 h2 PairH) -> Ordering
comparePairs {h1} {h2} x y = let ((x1::xs), kickers1) = getMatchAndRest2 h1 x
                                 ((y1::ys), kickers2) = getMatchAndRest2 h2 y in
                                 (case compare (cardValue x1) (cardValue y1) of
                                        LT => LT
                                        EQ => compareHighCards kickers1 kickers2
                                        GT => GT)


getHighLowPair: Card -> Card -> (Card, Card)
getHighLowPair x y = case compare (cardValue x) (cardValue y) of
               LT => (y, x)
               gtOrEq => (x, y)

compareTwoPairs : {h1, h2: Vect HAND_SIZE Card} -> (x : TwoPair h1) -> (y : TwoPair h2) -> Ordering
compareTwoPairs {h1} {h2} (MkTwoPair x firstPair1 secondPair1)
                (MkTwoPair y firstPair2 secondPair2) = let (firstmatch1::f1) = getMatch2 h1 firstPair1
                                                           (secondmatch1::s1, kicker1::[]) = getMatchAndRest2 (getRest2 h1 firstPair1) secondPair1
                                                           (firstmatch2::f2) = getMatch2 h2 firstPair2
                                                           (secondmatch2::s2, kicker2::[]) = getMatchAndRest2 (getRest2 h2 firstPair2) secondPair2
                                                           (highestPair1, lowestPair1) = getHighLowPair firstmatch1 secondmatch1
                                                           (highestPair2, lowestPair2) = getHighLowPair firstmatch2 secondmatch2
                                                           in
                                                           (case compare (cardValue highestPair1) (cardValue highestPair2) of
                                                                 LT => LT
                                                                 GT => GT
                                                                 EQ => (case compare (cardValue lowestPair1) (cardValue lowestPair2) of
                                                                             LT => LT
                                                                             EQ => compare (cardValue kicker1) (cardValue kicker2)
                                                                             GT => GT))

compareThreeOfAKinds : {h1, h2: Vect (S(S(S n))) Card} -> (x : SlideWise3 h1 ThreeOfAKind) -> (y : SlideWise3 h2 ThreeOfAKind) -> Ordering
compareThreeOfAKinds {h1} {h2} x y = let ((x1::xs), kickers1) = getMatchAndRest3 h1 x
                                         ((y1::ys), kickers2) = getMatchAndRest3 h2 y in
                                          (case compare (cardValue x1) (cardValue y1) of
                                              LT => LT
                                              EQ => compareHighCards kickers1 kickers2
                                              GT => GT)

comparePairHs : (pair_prf1 : PairH h1) -> (pair_prf2 : PairH h2) -> Ordering
comparePairHs {h1} {h2} pair_prf1 pair_prf2 = compareHighCards h1 h2

compareFullHouseHands : (x : FullHouse h1) -> (y : FullHouse h2) -> Ordering
compareFullHouseHands {h1} (MkFullHouse x three_prf1 pair_prf1)
                      {h2} (MkFullHouse y three_prf2 pair_prf2) = let (threeCard1::_) = (getMatch3 h1 three_prf1)
                                                                      (threeCard2::_) = (getMatch3 h2 three_prf2) in
                                                                      (case compare (cardValue threeCard1) (cardValue threeCard2) of
                                                                            LT => LT
                                                                            EQ => comparePairHs pair_prf1 pair_prf2
                                                                            GT => GT)


compareStraights : {h1, h2: Vect HAND_SIZE Card} -> (x : Straight h1) -> (y : Straight h2) -> Ordering
compareStraights {h1} {h2} x y = compareHighCards h1 h2

export compareHands: {h1, h2: Vect HAND_SIZE Card} -> (hand1: Hand h1) -> (hand2: Hand h2) -> Ordering
compareHands (StraightFlushHand x) (StraightFlushHand y) = compareStraightFlushes x y
compareHands (StraightFlushHand x) hand2 = GT
compareHands (FourOfAKindHand x) (StraightFlushHand y) = LT
compareHands (FourOfAKindHand x) (FourOfAKindHand y) = compareFourOfAKinds x y
compareHands (FourOfAKindHand x) hand2 = GT
compareHands (FullHouseHand x) (StraightFlushHand y) = LT
compareHands (FullHouseHand x) (FourOfAKindHand y) = LT
compareHands (FullHouseHand x) (FullHouseHand y) = compareFullHouseHands x y
compareHands (FullHouseHand x) hand2 = GT
compareHands (FlushHand x) (StraightFlushHand y) = LT
compareHands (FlushHand x) (FourOfAKindHand y) = LT
compareHands (FlushHand x) (FullHouseHand y) = LT
compareHands (FlushHand x) (FlushHand y) = compareFlushes x y
compareHands (FlushHand x) hand2 = GT
compareHands (StraightHand x) (StraightFlushHand y) = LT
compareHands (StraightHand x) (FourOfAKindHand y) = LT
compareHands (StraightHand x) (FullHouseHand y) = LT
compareHands (StraightHand x) (FlushHand y) = LT
compareHands (StraightHand x) (StraightHand y) = compareStraights x y
compareHands (StraightHand x) hand2 = GT
compareHands (ThreeOfAKindHand x) (StraightFlushHand y) = LT
compareHands (ThreeOfAKindHand x) (FourOfAKindHand y) = LT
compareHands (ThreeOfAKindHand x) (FullHouseHand y) = LT
compareHands (ThreeOfAKindHand x) (FlushHand y) = LT
compareHands (ThreeOfAKindHand x) (StraightHand y) = LT
compareHands (ThreeOfAKindHand x) (ThreeOfAKindHand y) = compareThreeOfAKinds x y
compareHands (ThreeOfAKindHand x) hand2 = GT
compareHands (TwoPairHand x) (HighCardHand h2) = GT
compareHands (TwoPairHand x) (PairHand y) = GT
compareHands (TwoPairHand x) (TwoPairHand y) = compareTwoPairs x y
compareHands (TwoPairHand x) hand2 = LT
compareHands (PairHand x) (HighCardHand h2) = GT
compareHands (PairHand x) (PairHand y) = comparePairs x y
compareHands (PairHand x) hand2 = LT
compareHands (HighCardHand h1) (HighCardHand h2) = compareHighCards h1 h2
compareHands (HighCardHand h1) hand2 = LT

showHighCard : (h : Vect HAND_SIZE Card) -> String
showHighCard (x :: xs) = "High Card: " ++ (show (cardValue x))


showPair :{h: Vect HAND_SIZE Card} -> (x : SlideWise2 h PairH) -> String
showPair {h} x = let (m::ms, r::rs) = getMatchAndRest2 h x in
                "Pair: " ++ (show (cardValue m)) ++ "s with a " ++ (show (cardValue r)) ++ " kicker"

showTwoPair : (x : TwoPair h)-> String
showTwoPair {h} (MkTwoPair x firstPair secondPair) = let (m1::ms1) = getMatch2 h firstPair
                                                         (m2::ms2, [kicker]) = getMatchAndRest2 (getRest2 h firstPair) secondPair in
                                                         "Two Pair: " ++ (show (cardValue m1)) ++ "s and " ++ (show (cardValue m2)) ++ "s with a " ++ (show (cardValue kicker)) ++ " kicker"

showThreeOfAKind : (x : SlideWise3 h ThreeOfAKind) -> String
showThreeOfAKind {h} x = let (m::ms, r::rs) = getMatchAndRest3 h x in
                "Three of a kind: " ++ (show (cardValue m)) ++ "s with a " ++ (show (cardValue r)) ++ " kicker"

showStraight : (x : Straight h) -> String
showStraight {h = (z :: xs)} (MkStraight x y) = "Straight: " ++ (show (cardValue z)) ++ " high"

showFlush : (x : Flush h) -> String
showFlush {h = (y :: xs)} x = "Flush: " ++ (show (cardValue y)) ++ " high"



showFullHouse : (x : FullHouse h) -> String
showFullHouse {h} (MkFullHouse x three pair) = let (m1::m1s) = getMatch3 h three
                                                   (m2::m2s) = (getRest3 h three) in
                                                   "Full house: " ++ (show (cardValue m1)) ++ "s over " ++ (show (cardValue m2)) ++ "s"

showFourOfAKind : (x : SlideWise4 h FourOfAKind) -> String
showFourOfAKind {h} x = let (m::ms, [kicker]) = getMatchAndRest4 h x in
                "Four of a kind: " ++ (show (cardValue m)) ++ "s with a " ++ (show (cardValue kicker)) ++ " kicker"

showStraightFlush : (x : StraightFlush h) -> String
showStraightFlush {h = (y :: xs)} x = "Straight flush: " ++ (show (cardValue y)) ++ " high"

export Show (Hand h) where
  show (StraightFlushHand x) = showStraightFlush x
  show (FourOfAKindHand x) = showFourOfAKind x
  show (FullHouseHand x) = showFullHouse x
  show (FlushHand x) = showFlush x
  show (StraightHand x) = showStraight x
  show (ThreeOfAKindHand x) = showThreeOfAKind x
  show (TwoPairHand x) = showTwoPair x
  show (PairHand x) = showPair x
  show (HighCardHand h) = showHighCard h
