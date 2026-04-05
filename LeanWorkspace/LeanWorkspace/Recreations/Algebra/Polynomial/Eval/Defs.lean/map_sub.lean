import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Ring R] {p q r : R[X]}

theorem map_sub {S} [Ring S] (f : R →+* S) : (p - q).map f = p.map f - q.map f := (Polynomial.mapRingHom f).map_sub p q

