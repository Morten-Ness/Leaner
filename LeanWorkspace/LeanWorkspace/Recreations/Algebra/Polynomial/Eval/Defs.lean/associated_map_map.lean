import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem associated_map_map (f : R →+* S) {x y : R[X]} :
    Associated x y → Associated (x.map f) (y.map f) := .map (Polynomial.mapRingHom f)

