import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

variable (A : Matrix n n α) (b : n → α)

theorem sum_cramer {β} (s : Finset β) (f : β → n → α) :
    (∑ x ∈ s, Matrix.cramer A (f x)) = Matrix.cramer A (∑ x ∈ s, f x) := (map_sum (Matrix.cramer A) ..).symm

