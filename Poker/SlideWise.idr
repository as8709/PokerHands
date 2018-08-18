module SlideWise

import Data.Vect

public export data SlideWise2: Vect (S (S n)) e -> (Vect 2 e -> Type) -> Type where
  HeadMatches2: (searched: Vect (S (S m)) e) -> (match: Vect 2 e) -> (rest:Vect m e) -> prf match  -> SlideWise2 (match++rest) prf
  RestMatches2: (x:e) -> (rest: Vect (S (S n)) e) -> SlideWise2 rest prf -> SlideWise2 (x::rest) prf


export getMatchAndRest2: (xs: Vect (S (S n)) e) -> (prf: SlideWise2 xs prfT) -> (Vect 2 e, Vect n e)
getMatchAndRest2 (match ++ rest) (HeadMatches2 searched match rest x) = (match, rest)
getMatchAndRest2 (x :: rest) (RestMatches2 x rest prf) = let (match, rest') = getMatchAndRest2 rest prf in
                                                                 (match, x::rest')

export getRest2: (xs: Vect (S (S n)) e) -> (prf: SlideWise2 xs prfT) -> Vect n e
getRest2 (match ++ rest) (HeadMatches2 searched match rest x) = rest
getRest2 (x :: rest) (RestMatches2 x rest prf) = x::(getRest2 rest prf)

export getMatch2: (xs: Vect (S (S n)) e) -> (prf: SlideWise2 xs prfT) -> Vect 2 e
getMatch2 (match ++ rest) (HeadMatches2 searched match rest x) = match
getMatch2 (x :: rest) (RestMatches2 x rest prf) = getMatch2 rest prf

reachedEnd2 : (contra : prfT ([x1, x2]) -> Void) -> SlideWise2 [x1, x2] prfT -> Void
reachedEnd2 contra (HeadMatches2 sorted (x1:: x2 :: []) [] prf) = contra prf

notInHeadOrRest2 : (contra : SlideWise2 (x2 :: (x3 :: xs)) prfT -> Void) -> (head_contra : prfT [x1, x2] -> Void) -> SlideWise2 (x1 :: (x2 :: (x3 :: xs))) prfT -> Void
notInHeadOrRest2 contra head_contra (RestMatches2 x1 (x2 :: (x3 :: xs)) x) = contra x

export isSlideWise2: (xs: Vect (S (S n)) e) -> (prfFun: (y:Vect 2 e) -> Dec (prfT y)) -> Dec (SlideWise2 xs prfT)
isSlideWise2 {n = Z} (x1 :: x2:: []) prfFun = case prfFun [x1, x2] of
                                                (Yes prf) => Yes (HeadMatches2 [x1, x2] [x1, x2] [] prf)
                                                (No contra) => No (reachedEnd2 contra)
isSlideWise2 {n = (S k)} (x1 :: x2 :: x3 :: xs) prfFun = case prfFun [x1, x2] of
                                                              (Yes prf) => Yes (HeadMatches2 (x1 :: x2 :: x3 :: xs) [x1, x2] (x3::xs) prf)
                                                              (No head_contra) => (case isSlideWise2 (x2::x3::xs) prfFun of
                                                                                   (Yes prf) => Yes (RestMatches2 x1 (x2::x3::xs) prf)
                                                                                   (No contra) => No (notInHeadOrRest2 contra head_contra))


public export data SlideWise3: Vect (S (S (S n))) e -> (Vect 3 e -> Type) -> Type where
 HeadMatches3: (searched: Vect (S (S (S m))) e) -> (match: Vect 3 e) -> (rest:Vect m e) -> prf match  -> SlideWise3 (match++rest) prf
 RestMatches3: (x:e) -> (rest: Vect (S (S (S n))) e) -> SlideWise3 rest prf -> SlideWise3 (x::rest) prf


export getMatchAndRest3:(xs: Vect (S (S (S n))) e) -> (prf: SlideWise3 xs prfT) -> (Vect 3 e, Vect n e)
getMatchAndRest3 (match ++ rest) (HeadMatches3 searched match rest x) = (match, rest)
getMatchAndRest3 (x :: rest) (RestMatches3 x rest prf) = let (match, rest') = getMatchAndRest3 rest prf in
                                                                (match, x::rest')

export getRest3: (xs: Vect (S (S (S n))) e) -> (prf: SlideWise3 xs prfT) -> Vect n e
getRest3 (match ++ rest) (HeadMatches3 searched match rest x) = rest
getRest3 (x :: rest) (RestMatches3 x rest prf) = let rest' = getRest3 rest prf in
                                                                x::rest'


export getMatch3:(xs: Vect (S (S (S n))) e) -> (prf: SlideWise3 xs prfT) -> Vect 3 e
getMatch3 (match ++ rest) (HeadMatches3 searched match rest x) = match
getMatch3 (x :: rest) (RestMatches3 x rest prf) = let match = getMatch3 rest prf in
                                                            match

reachedEnd3 : (contra : prfT [x1, x2, x3] -> Void) -> SlideWise3 [x1, x2, x3] prfT -> Void
reachedEnd3 contra (HeadMatches3 sorted (x1:: x2 :: x3 :: []) [] prf) = contra prf

notInHeadOrRest3 : (contra : SlideWise3 (x2 :: (x3 :: (x4 :: xs))) prfT -> Void) -> (head_contra : prfT [x1, x2, x3] -> Void) -> SlideWise3 (x1 :: (x2 :: (x3 :: (x4 :: xs)))) prfT -> Void
notInHeadOrRest3 contra head_contra (RestMatches3 x1 (x2 :: (x3 :: (x4 :: xs))) x) = contra x

export isSlideWise3: (xs: Vect (S (S (S n))) e) -> (prfFun: (y:Vect 3 e) -> Dec (prfT y)) -> Dec (SlideWise3 xs prfT)
isSlideWise3 {n = Z} (x1::x2::x3::[]) prfFun = case prfFun [x1, x2, x3] of
                                                    (Yes prf) => Yes (HeadMatches3 [x1, x2, x3] [x1, x2, x3] [] prf)
                                                    (No contra) => No (reachedEnd3 contra)
isSlideWise3 {n = (S k)} (x1::x2::x3::x4::xs) prfFun = case prfFun [x1, x2, x3] of
                                          (Yes prf) => Yes (HeadMatches3 (x1::x2::x3::x4::xs) [x1, x2, x3] (x4::xs) prf)
                                          (No head_contra) => (case isSlideWise3 (x2::x3::x4::xs) prfFun of
                                                               (Yes prf) => Yes (RestMatches3 x1 (x2::x3::x4::xs) prf)
                                                               (No contra) => No (notInHeadOrRest3 contra head_contra))

public export data SlideWise4: Vect (S (S (S (S n)))) e -> (Vect 4 e -> Type) -> Type where
  HeadMatches4: (searched: Vect (S (S (S (S m)))) e) -> (match: Vect 4 e) -> (rest:Vect m e) -> prf match  -> SlideWise4 (match++rest) prf
  RestMatches4: (x:e) -> (rest: Vect (S (S (S (S n)))) e) -> SlideWise4 rest prf -> SlideWise4 (x::rest) prf


export getMatchAndRest4:(xs: Vect (S (S (S (S n)))) e) -> (prf: SlideWise4 xs prfT) -> (Vect 4 e, Vect n e)
getMatchAndRest4 (match ++ rest) (HeadMatches4 searched match rest x) = (match, rest)
getMatchAndRest4 (x :: rest) (RestMatches4 x rest prf) = let (match, rest') = getMatchAndRest4 rest prf in
                                                               (match, x::rest')


reachedEnd4 : (contra : prfT (x1::x2::x3::x4::[]) -> Void) -> SlideWise4 (x1::x2::x3::x4::[]) prfT -> Void
reachedEnd4 contra (HeadMatches4 sorted (x1::x2::x3::x4::[]) [] prf) = contra prf


notInHeadOrRest4 : (contra : SlideWise4 (x2 :: (x3 :: (x4 :: (x5 :: xs)))) prfT -> Void) -> (head_contra : prfT [x1, x2, x3, x4] -> Void) -> SlideWise4 (x1 :: (x2 :: (x3 :: (x4 :: (x5 :: xs))))) prfT -> Void
notInHeadOrRest4 contra head_contra (RestMatches4 x1 (x2 :: (x3 :: (x4 :: (x5 :: xs)))) x) = contra x


export isSlideWise4: (xs: Vect (S (S (S (S n)))) e) -> (prfFun: (y:Vect 4 e) -> Dec (prfT y)) -> Dec (SlideWise4 xs prfT)
isSlideWise4 {n = Z} (x1::x2::x3::x4::[]) prfFun = case prfFun [x1, x2, x3, x4] of
                                                   (Yes prf) => Yes (HeadMatches4 [x1, x2, x3, x4] [x1, x2, x3, x4] [] prf)
                                                   (No contra) => No (reachedEnd4 contra)
isSlideWise4 {n = (S k)} (x1::x2::x3::x4::x5::xs) prfFun = case prfFun [x1, x2, x3, x4] of
                                         (Yes prf) => Yes (HeadMatches4 (x1::x2::x3::x4::x5::xs) [x1, x2, x3, x4] (x5::xs) prf)
                                         (No head_contra) => (case isSlideWise4 (x2::x3::x4::x5::xs) prfFun of
                                                              (Yes prf) => Yes (RestMatches4 x1 (x2::x3::x4::x5::xs) prf)
                                                              (No contra) => No (notInHeadOrRest4 contra head_contra))
