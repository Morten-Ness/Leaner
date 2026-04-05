import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem map_pow (n : ℕ) : (p ^ n).map f = p.map f ^ n := (Polynomial.mapRingHom f).map_pow _ _

