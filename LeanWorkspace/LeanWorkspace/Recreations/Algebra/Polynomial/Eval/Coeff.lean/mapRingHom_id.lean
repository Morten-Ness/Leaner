import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem mapRingHom_id : mapRingHom (RingHom.id R) = RingHom.id R[X] := RingHom.ext fun _x => Polynomial.map_id

