import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] [IsSimpleRing R] [Semiring S] [Nontrivial S] {p q : R[X]}

theorem map_eq_zero (f : R →+* S) : p.map f = 0 ↔ p = 0 := Polynomial.map_eq_zero_iff f.injective

