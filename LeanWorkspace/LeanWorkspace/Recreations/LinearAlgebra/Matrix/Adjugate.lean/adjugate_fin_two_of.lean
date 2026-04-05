import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_fin_two_of (a b c d : α) : Matrix.adjugate !![a, b; c, d] = !![d, -b; -c, a] := Matrix.adjugate_fin_two _

