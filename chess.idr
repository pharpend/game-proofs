module Chess

import Data.Fin
import Data.Matrix
import Data.Vect

||| The color of the piece is either black or white
data Color = Black | White

||| The possible piece shapes
data Shape
  = Rook
  | Knight
  | Bishop
  | Queen
  | King
  | Pawn

record Piece where
  constructor MkPiece
  pieceColor : Color
  pieceShape : Shape

Square : Type
Square = Maybe Piece

ChessBoard : Type
ChessBoard = Matrix 8 8 Square

toFEN : Square -> Char
toFEN Nothing = ' '
toFEN (Just (MkPiece Black Rook)) = 'r'
toFEN (Just (MkPiece Black Knight)) = 'n'
toFEN (Just (MkPiece Black Bishop)) = 'b'
toFEN (Just (MkPiece Black Queen)) = 'q'
toFEN (Just (MkPiece Black King)) = 'k'
toFEN (Just (MkPiece Black Pawn)) = 'p'
toFEN (Just (MkPiece White Rook)) = 'R'
toFEN (Just (MkPiece White Knight)) = 'N'
toFEN (Just (MkPiece White Bishop)) = 'B'
toFEN (Just (MkPiece White Queen)) = 'Q'
toFEN (Just (MkPiece White King)) = 'K'
toFEN (Just (MkPiece White Pawn)) = 'P'

fromFEN : Char -> Maybe Square
fromFEN ' ' = Just Nothing
fromFEN 'r' = Just (Just (MkPiece Black Rook))
fromFEN 'n' = Just (Just (MkPiece Black Knight))
fromFEN 'b' = Just (Just (MkPiece Black Bishop))
fromFEN 'q' = Just (Just (MkPiece Black Queen))
fromFEN 'k' = Just (Just (MkPiece Black King))
fromFEN 'p' = Just (Just (MkPiece Black Pawn))
fromFEN 'R' = Just (Just (MkPiece White Rook))
fromFEN 'N' = Just (Just (MkPiece White Knight))
fromFEN 'B' = Just (Just (MkPiece White Bishop))
fromFEN 'Q' = Just (Just (MkPiece White Queen))
fromFEN 'K' = Just (Just (MkPiece White King))
fromFEN 'P' = Just (Just (MkPiece White Pawn))
fromFEN _ = Nothing

toFEN_fromFEN_isomorph : 
  (s : Square) -> 
  fromFEN (toFEN s) = Just s
toFEN_fromFEN_isomorph Nothing = Refl
toFEN_fromFEN_isomorph (Just (MkPiece Black Rook)) = Refl
toFEN_fromFEN_isomorph (Just (MkPiece Black Knight)) = Refl
toFEN_fromFEN_isomorph (Just (MkPiece Black Bishop)) = Refl
toFEN_fromFEN_isomorph (Just (MkPiece Black Queen)) = Refl
toFEN_fromFEN_isomorph (Just (MkPiece Black King)) = Refl
toFEN_fromFEN_isomorph (Just (MkPiece Black Pawn)) = Refl
toFEN_fromFEN_isomorph (Just (MkPiece White Rook)) = Refl
toFEN_fromFEN_isomorph (Just (MkPiece White Knight)) = Refl
toFEN_fromFEN_isomorph (Just (MkPiece White Bishop)) = Refl
toFEN_fromFEN_isomorph (Just (MkPiece White Queen)) = Refl
toFEN_fromFEN_isomorph (Just (MkPiece White King)) = Refl
toFEN_fromFEN_isomorph (Just (MkPiece White Pawn)) = Refl
