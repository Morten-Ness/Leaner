import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem rootMultiplicity_zero {x : R} : Polynomial.rootMultiplicity x 0 = 0 := dif_pos rfl

