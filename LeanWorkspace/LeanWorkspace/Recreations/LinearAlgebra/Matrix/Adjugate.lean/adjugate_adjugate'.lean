import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_adjugate' (A : Matrix n n α) [Nontrivial n] :
    Matrix.adjugate (Matrix.adjugate A) = det A ^ (Fintype.card n - 2) • A := Matrix.adjugate_adjugate _ <| Fintype.one_lt_card.ne'

