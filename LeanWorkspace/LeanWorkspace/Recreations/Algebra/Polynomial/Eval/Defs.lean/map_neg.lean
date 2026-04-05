import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Ring R] {p q r : R[X]}

theorem map_neg {S} [Ring S] (f : R →+* S) : (-p).map f = -p.map f := (Polynomial.mapRingHom f).map_neg p

