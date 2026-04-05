import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] [IsSimpleRing R] [Semiring S] [Nontrivial S] {p q : R[X]}

theorem nextCoeff_map_eq (p : R[X]) (f : R →+* S) : (p.map f).nextCoeff = f p.nextCoeff := nextCoeff_map f.injective _

