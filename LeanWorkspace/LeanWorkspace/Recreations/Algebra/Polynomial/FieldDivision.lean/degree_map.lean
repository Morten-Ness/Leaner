import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {k : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] [IsSimpleRing R] [Semiring S] [Nontrivial S] {p q : R[X]}

theorem degree_map (p : R[X]) (f : R →+* S) : (p.map f).degree = p.degree := degree_map_eq_of_injective f.injective _

