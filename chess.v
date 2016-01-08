Inductive color :=
| black
| white.

Inductive shape :=
| rook
| knight
| bishop
| queen
| king
| pawn.

Record piece : Type :=
  { piece_color : color
  ; piece_shape : shape
  }.

Definition square : Type := option piece.

Definition fin (n : nat) : Set := { n' : nat | n' < n }.

Fixpoint vect_index {n : nat} {t : Type}
           (v : vect (S n) t) (n' : fin n) : t :=
  match v with
    | cons x xs =>
      match n' with
        | Z => x
        | S n'' => vect_index xs n''
      end
  end.


Proof.
  intros.
  destruct v as [v' | v''].

Definition matrix (r : nat) (c : nat) (t : Type) : Type :=
  vect r (vect c t).
    
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
