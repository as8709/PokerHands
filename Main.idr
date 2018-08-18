module Main
import Data.Vect

import Poker.Hands
import Poker.Card
import Poker.InsertionSort
import Poker.Sorted
import Poker.ElemsAreSame



--=======================================================================================================
--=======================================================================================================
--Utility functions
--=======================================================================================================
--=======================================================================================================
parseCardValue: Char -> Either String Value
parseCardValue 'A' = Right Ace
parseCardValue 'K' = Right King
parseCardValue 'Q' = Right Queen
parseCardValue 'J' = Right Jack
parseCardValue '2' = Right (Pip 2)
parseCardValue '3' = Right (Pip 3)
parseCardValue '4' = Right (Pip 4)
parseCardValue '5' = Right (Pip 5)
parseCardValue '6' = Right (Pip 6)
parseCardValue '7' = Right (Pip 7)
parseCardValue '8' = Right (Pip 8)
parseCardValue '9' = Right (Pip 9)
parseCardValue 'T' = Right (Pip 10)
parseCardValue x = Left "Invalid value character"

parseCardSuit: Char -> Either String Suit
parseCardSuit 'C' = Right Clubs
parseCardSuit 'D' = Right Diamonds
parseCardSuit 'H' = Right Hearts
parseCardSuit 'S' = Right Spades
parseCardSuit x = Left "Invalid suit character"

||| Attempt to parse a single card description
parseCard: List Char -> Either String Card
parseCard [] = Left "Card description must be two characters"
parseCard (c1 :: c2 :: []) = (case parseCardValue c1 of
                                   (Left l) => Left l
                                   (Right value) => (case parseCardSuit c2 of
                                                      (Left l) => Left l
                                                      (Right suit) => Right (MkCard value suit) ))
parseCard xs = Left "Card description must be two characters"

parseHand': (input: List (List Char)) -> (aux: List Card) -> Either String (List Card)
parseHand' [] aux = Right aux
parseHand' (x :: xs) aux = case parseCard x of
                                (Left l) => Left l
                                (Right r) => parseHand' xs (r::aux)


parseHand: String -> Either String (Vect HAND_SIZE Card)
parseHand x = let unparsedCards = words' (unpack x) in
                (case parseHand' unparsedCards [] of
                     Left l => Left l
                     Right [x1, x2, x3, x4, x5] => Right [x1, x2, x3, x4, x5]
                     Right xs => Left "Wrong number of cards in hand")



parseEvalHand: String -> Either String (hand:(Vect HAND_SIZE Card) ** Hand hand)
parseEvalHand x = case parseHand x of
                       (Left l) => Left l
                       (Right r) => let (hand ** (sort_prf, elem_prf)) = insertSort r
                                        evaled = evalHand hand sort_prf in
                                        Right (hand ** evaled)
getHand: IO (Either String (hand:(Vect HAND_SIZE Card) ** Hand hand))
getHand = do
            putStrLn "Enter hand"
            cardsString <- getLine
            pure (parseEvalHand cardsString)

getComparison: IO ()
getComparison = do
      Right (h1 ** hand1) <- getHand | Left l => putStrLn l
      Right (h2 ** hand2) <- getHand | Left l => putStrLn l
      case compareHands hand1 hand2 of
          LT => putStrLn ("Player 2 wins with:" ++ (show hand2))
          EQ => putStrLn "Tie"
          GT => putStrLn ("Player 1 wins with:" ++ (show hand1))

main: IO ()
main = getComparison
