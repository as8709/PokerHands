module Card

import Data.Vect

public export data Value: Type where
  Pip: (v: Nat) -> Value
  Jack: Value
  Queen: Value
  King: Value
  Ace: Value

public export data Suit = Clubs
  | Spades
  | Hearts
  | Diamonds

public export record Card where
  constructor  MkCard
  value : Value
  suit : Suit

||| proof that the first card is consecutive with the second
||| only valid if the first card is higher
export data ConsecComp: Card -> Card -> Type where
  PipConsec: ConsecComp (MkCard (Pip (S x)) _) (MkCard (Pip x) _)
  JackTen: ConsecComp (MkCard Jack _) (MkCard (Pip 10) _)
  QueenJack: ConsecComp (MkCard Queen _) (MkCard Jack _)
  KingQueen: ConsecComp (MkCard King _) (MkCard Queen _)
  AceKing: ConsecComp (MkCard Ace _) (MkCard King _)

export data Consecutive : Vect n Card -> Type where
  Comp : (x: Card) -> Consecutive (y :: ys) -> ConsecComp x y -> Consecutive (x :: y :: ys)
  ConSingle: (x: Card) -> Consecutive [x]
  ConEmpty : Consecutive []


clubsSpades : (Clubs = Spades) -> Void
clubsSpades Refl impossible

clubsHearts : (Clubs = Hearts) -> Void
clubsHearts Refl impossible

clubsDiamonds : (Clubs = Diamonds) -> Void
clubsDiamonds Refl impossible

spadesClubs : (Spades = Clubs) -> Void
spadesClubs Refl impossible

spadesHearts : (Spades = Hearts) -> Void
spadesHearts Refl impossible

spadesDiamonds : (Spades = Diamonds) -> Void
spadesDiamonds Refl impossible

heartsClubs : (Hearts = Clubs) -> Void
heartsClubs Refl impossible

heartsSpades : (Hearts = Spades) -> Void
heartsSpades Refl impossible

heartsDiamonds : (Hearts = Diamonds) -> Void
heartsDiamonds Refl impossible

diamondsClubs : (Diamonds = Clubs) -> Void
diamondsClubs Refl impossible

diamondsSpades : (Diamonds = Spades) -> Void
diamondsSpades Refl impossible

diamondsHearts : (Diamonds = Hearts) -> Void
diamondsHearts Refl impossible

export DecEq Suit where
  decEq Clubs Clubs = Yes Refl
  decEq Clubs Spades = No clubsSpades
  decEq Clubs Hearts = No clubsHearts
  decEq Clubs Diamonds = No clubsDiamonds
  decEq Spades Clubs = No spadesClubs
  decEq Spades Spades = Yes Refl
  decEq Spades Hearts = No spadesHearts
  decEq Spades Diamonds = No spadesDiamonds
  decEq Hearts Clubs = No heartsClubs
  decEq Hearts Spades = No heartsSpades
  decEq Hearts Hearts = Yes Refl
  decEq Hearts Diamonds = No heartsDiamonds
  decEq Diamonds Clubs = No diamondsClubs
  decEq Diamonds Spades = No diamondsSpades
  decEq Diamonds Hearts = No diamondsHearts
  decEq Diamonds Diamonds = Yes Refl

pipsDontMatch : (contra : (v1 = v2) -> Void) -> (Pip v1 = Pip v2) -> Void
pipsDontMatch contra Refl = contra Refl

pipJack : (Pip v = Jack) -> Void
pipJack Refl impossible

pipQueen : (Pip v = Queen) -> Void
pipQueen Refl impossible

pipKing : (Pip v = King) -> Void
pipKing Refl impossible

pipAce : (Pip v = Ace) -> Void
pipAce Refl impossible

jackPip : (Jack = Pip v) -> Void
jackPip Refl impossible

jackQueen : (Jack = Queen) -> Void
jackQueen Refl impossible

jackKing : (Jack = King) -> Void
jackKing Refl impossible

jackAce : (Jack = Ace) -> Void
jackAce Refl impossible

queenPip : (Queen = Pip v) -> Void
queenPip Refl impossible

queenJack : (Queen = Jack) -> Void
queenJack Refl impossible

queenKing : (Queen = King) -> Void
queenKing Refl impossible

queenAce : (Queen = Ace) -> Void
queenAce Refl impossible

kingPip : (King = Pip v) -> Void
kingPip Refl impossible

kingJack : (King = Jack) -> Void
kingJack Refl impossible

kingQueen : (King = Queen) -> Void
kingQueen Refl impossible

kingAce : (King = Ace) -> Void
kingAce Refl impossible

acePip : (Ace = Pip v) -> Void
acePip Refl impossible

aceJack : (Ace = Jack) -> Void
aceJack Refl impossible

aceQueen : (Ace = Queen) -> Void
aceQueen Refl impossible

aceKing : (Ace = King) -> Void
aceKing Refl impossible

export DecEq Value where
  decEq (Pip v1) (Pip v2) = case decEq v1 v2 of
                                 (Yes prf) => Yes (rewrite prf in Refl)
                                 (No contra) => No (pipsDontMatch contra)
  decEq (Pip v) Jack = No pipJack
  decEq (Pip v) Queen = No pipQueen
  decEq (Pip v) King = No pipKing
  decEq (Pip v) Ace = No pipAce
  decEq Jack (Pip v) = No jackPip
  decEq Jack Jack = Yes Refl
  decEq Jack Queen = No jackQueen
  decEq Jack King = No jackKing
  decEq Jack Ace = No jackAce
  decEq Queen (Pip v) = No queenPip
  decEq Queen Jack = No queenJack
  decEq Queen Queen = Yes Refl
  decEq Queen King = No queenKing
  decEq Queen Ace = No queenAce
  decEq King (Pip v) = No kingPip
  decEq King Jack = No kingJack
  decEq King Queen = No kingQueen
  decEq King King = Yes Refl
  decEq King Ace = No kingAce
  decEq Ace (Pip v) = No acePip
  decEq Ace Jack = No aceJack
  decEq Ace Queen = No aceQueen
  decEq Ace King = No aceKing
  decEq Ace Ace = Yes Refl

export valueToNum : Value -> Nat
valueToNum (Pip v) = v
valueToNum Jack = 11
valueToNum Queen = 12
valueToNum King = 13
valueToNum Ace = 14

export cardValue : Card -> Nat
cardValue (MkCard value suit) = valueToNum value

--=======================================================================================================
-- isConsecutive
--=======================================================================================================
pipsNonConsec : (contra : (v = S k) -> Void) -> ConsecComp (MkCard (Pip v) suit) (MkCard (Pip k) suit1) -> Void
pipsNonConsec contra PipConsec = contra Refl

pipThenJack : ConsecComp (MkCard (Pip v) suit) (MkCard Jack suit1) -> Void
pipThenJack PipConsec impossible
pipThenJack JackTen impossible
pipThenJack QueenJack impossible
pipThenJack KingQueen impossible
pipThenJack AceKing impossible

pipThenQueen : ConsecComp (MkCard (Pip v) suit) (MkCard Queen suit1) -> Void
pipThenQueen PipConsec impossible
pipThenQueen JackTen impossible
pipThenQueen QueenJack impossible
pipThenQueen KingQueen impossible
pipThenQueen AceKing impossible

pipThenKing : ConsecComp (MkCard (Pip v) suit) (MkCard King suit1) -> Void
pipThenKing PipConsec impossible
pipThenKing JackTen impossible
pipThenKing QueenJack impossible
pipThenKing KingQueen impossible
pipThenKing AceKing impossible

pipThenAce : ConsecComp (MkCard (Pip v) suit) (MkCard Ace suit1) -> Void
pipThenAce PipConsec impossible
pipThenAce JackTen impossible
pipThenAce QueenJack impossible
pipThenAce KingQueen impossible
pipThenAce AceKing impossible

jackThenNotTen : (contra : (v = the Nat (fromInteger 10)) -> Void) -> ConsecComp (MkCard Jack suit) (MkCard (Pip v) suit1) -> Void
jackThenNotTen contra JackTen = contra Refl

bothJacks : ConsecComp (MkCard Jack suit) (MkCard Jack suit1) -> Void
bothJacks PipConsec impossible
bothJacks JackTen impossible
bothJacks QueenJack impossible
bothJacks KingQueen impossible
bothJacks AceKing impossible

jackThenQueen : ConsecComp (MkCard Jack suit) (MkCard Queen suit1) -> Void
jackThenQueen PipConsec impossible
jackThenQueen JackTen impossible
jackThenQueen QueenJack impossible
jackThenQueen KingQueen impossible
jackThenQueen AceKing impossible

jackThenKing : ConsecComp (MkCard Jack suit) (MkCard King suit1) -> Void
jackThenKing PipConsec impossible
jackThenKing JackTen impossible
jackThenKing QueenJack impossible
jackThenKing KingQueen impossible
jackThenKing AceKing impossible

jackThenAce : ConsecComp (MkCard Jack suit) (MkCard Ace suit1) -> Void
jackThenAce PipConsec impossible
jackThenAce JackTen impossible
jackThenAce QueenJack impossible
jackThenAce KingQueen impossible
jackThenAce AceKing impossible

queenThenPip : ConsecComp (MkCard Queen suit) (MkCard (Pip v) suit1) -> Void
queenThenPip PipConsec impossible
queenThenPip JackTen impossible
queenThenPip QueenJack impossible
queenThenPip KingQueen impossible
queenThenPip AceKing impossible

queenThenQueen : ConsecComp (MkCard Queen suit) (MkCard Queen suit1) -> Void
queenThenQueen PipConsec impossible
queenThenQueen JackTen impossible
queenThenQueen QueenJack impossible
queenThenQueen KingQueen impossible
queenThenQueen AceKing impossible

queenThenKing : ConsecComp (MkCard Queen suit) (MkCard King suit1) -> Void
queenThenKing PipConsec impossible
queenThenKing JackTen impossible
queenThenKing QueenJack impossible
queenThenKing KingQueen impossible
queenThenKing AceKing impossible

queenThenAce : ConsecComp (MkCard Queen suit) (MkCard Ace suit1) -> Void
queenThenAce PipConsec impossible
queenThenAce JackTen impossible
queenThenAce QueenJack impossible
queenThenAce KingQueen impossible
queenThenAce AceKing impossible

kingThenPip : ConsecComp (MkCard King suit) (MkCard (Pip v) suit1) -> Void
kingThenPip PipConsec impossible
kingThenPip JackTen impossible
kingThenPip QueenJack impossible
kingThenPip KingQueen impossible
kingThenPip AceKing impossible

kingThenJack : ConsecComp (MkCard King suit) (MkCard Jack suit1) -> Void
kingThenJack PipConsec impossible
kingThenJack JackTen impossible
kingThenJack QueenJack impossible
kingThenJack KingQueen impossible
kingThenJack AceKing impossible

kingThenKing : ConsecComp (MkCard King suit) (MkCard King suit1) -> Void
kingThenKing PipConsec impossible
kingThenKing JackTen impossible
kingThenKing QueenJack impossible
kingThenKing KingQueen impossible
kingThenKing AceKing impossible

kingThenAce : ConsecComp (MkCard King suit) (MkCard Ace suit1) -> Void
kingThenAce PipConsec impossible
kingThenAce JackTen impossible
kingThenAce QueenJack impossible
kingThenAce KingQueen impossible
kingThenAce AceKing impossible

aceThenPip : ConsecComp (MkCard Ace suit) (MkCard (Pip v) suit1) -> Void
aceThenPip PipConsec impossible
aceThenPip JackTen impossible
aceThenPip QueenJack impossible
aceThenPip KingQueen impossible
aceThenPip AceKing impossible

aceThenJack : ConsecComp (MkCard Ace suit) (MkCard Jack suit1) -> Void
aceThenJack PipConsec impossible
aceThenJack JackTen impossible
aceThenJack QueenJack impossible
aceThenJack KingQueen impossible
aceThenJack AceKing impossible

aceThenQueen : ConsecComp (MkCard Ace suit) (MkCard Queen suit1) -> Void
aceThenQueen PipConsec impossible
aceThenQueen JackTen impossible
aceThenQueen QueenJack impossible
aceThenQueen KingQueen impossible
aceThenQueen AceKing impossible

aceThenAce : ConsecComp (MkCard Ace suit) (MkCard Ace suit1) -> Void
aceThenAce PipConsec impossible
aceThenAce JackTen impossible
aceThenAce QueenJack impossible
aceThenAce KingQueen impossible
aceThenAce AceKing impossible

isConsecComp: (x:Card) -> (y: Card) -> Dec (ConsecComp x y)
isConsecComp (MkCard (Pip v) _) (MkCard (Pip k) _) = (case decEq v (S k) of
                                                               (Yes prf) => Yes (rewrite prf in PipConsec)
                                                               (No contra) => No (pipsNonConsec contra))
isConsecComp (MkCard (Pip v) _) (MkCard Jack _) = No pipThenJack
isConsecComp (MkCard (Pip v) _) (MkCard Queen _) = No pipThenQueen
isConsecComp (MkCard (Pip v) _) (MkCard King _) = No pipThenKing
isConsecComp (MkCard (Pip v) _) (MkCard Ace _) = No pipThenAce
isConsecComp (MkCard Jack _) (MkCard (Pip v) _) = case decEq v (the Nat 10) of
                                                       (Yes prf) => Yes (rewrite prf in JackTen)
                                                       (No contra) => No (jackThenNotTen contra)
isConsecComp (MkCard Jack _) (MkCard Jack _) = No bothJacks
isConsecComp (MkCard Jack _) (MkCard Queen _) = No jackThenQueen
isConsecComp (MkCard Jack _) (MkCard King _) = No jackThenKing
isConsecComp (MkCard Jack _) (MkCard Ace _) = No jackThenAce
isConsecComp (MkCard Queen _) (MkCard (Pip v) _) = No queenThenPip
isConsecComp (MkCard Queen _) (MkCard Jack _) = Yes QueenJack
isConsecComp (MkCard Queen _) (MkCard Queen _) = No queenThenQueen
isConsecComp (MkCard Queen _) (MkCard King _) = No queenThenKing
isConsecComp (MkCard Queen _) (MkCard Ace _) = No queenThenAce
isConsecComp (MkCard King _) (MkCard (Pip v) _) = No kingThenPip
isConsecComp (MkCard King _) (MkCard Jack _) = No kingThenJack
isConsecComp (MkCard King _) (MkCard Queen _) = Yes KingQueen
isConsecComp (MkCard King _) (MkCard King _) = No kingThenKing
isConsecComp (MkCard King _) (MkCard Ace _) = No kingThenAce
isConsecComp (MkCard Ace _) (MkCard (Pip v) _) = No aceThenPip
isConsecComp (MkCard Ace _) (MkCard Jack _) = No aceThenJack
isConsecComp (MkCard Ace _) (MkCard Queen _) = No aceThenQueen
isConsecComp (MkCard Ace _) (MkCard King _) = Yes AceKing
isConsecComp (MkCard Ace _) (MkCard Ace _) = No aceThenAce

headNotConsec : (contra : ConsecComp x x1 -> Void) -> Consecutive (x :: (x1 :: xs)) -> Void
headNotConsec contra (Comp x y z) = contra z

restIsNotConsec : (contra : Consecutive (x1 :: xs) -> Void) -> Consecutive (x :: (x1 :: xs)) -> Void
restIsNotConsec contra (Comp x y z) = contra y

export isConsecutive: (x:Vect n Card) -> Dec (Consecutive x)
isConsecutive [] = Yes ConEmpty
isConsecutive (x :: []) = Yes (ConSingle x)
isConsecutive (x :: x1 :: xs) = case isConsecComp x x1 of
                                     (Yes consec_prf) => (case isConsecutive (x1::xs) of
                                                               (Yes prf) => Yes (Comp x prf consec_prf)
                                                               (No contra) => No (restIsNotConsec contra))
                                     (No contra) => No (headNotConsec contra)


export Show Value where
  show (Pip v) = show v
  show Jack = "Jack"
  show Queen = "Queen"
  show King = "King"
  show Ace = "Ace"

Show Suit where
  show Clubs = "Clubs"
  show Spades = "Spades"
  show Hearts = "Hearts"
  show Diamonds = "Diamonds"

export Show Card where
  show (MkCard value suit) = "the " ++ (show value) ++ " of " ++ (show suit)
