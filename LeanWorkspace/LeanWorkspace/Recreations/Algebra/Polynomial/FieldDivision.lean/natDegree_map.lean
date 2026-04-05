import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] [IsSimpleRing R] [Semiring S] [Nontrivial S] {p q : R[X]}

theorem natDegree_map (f : R →+* S) : (p.map f).natDegree = p.natDegree := natDegree_map_eq_of_injective f.injective _

