import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] [IsSimpleRing R] [Semiring S] [Nontrivial S] {p q : R[X]}

theorem map_ne_zero {f : R →+* S} (hp : p ≠ 0) : p.map f ≠ 0 := mt (Polynomial.map_eq_zero f).1 hp

