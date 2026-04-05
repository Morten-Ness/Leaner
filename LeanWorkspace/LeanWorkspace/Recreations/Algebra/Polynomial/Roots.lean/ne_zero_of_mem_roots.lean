import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem ne_zero_of_mem_roots (h : a ∈ p.roots) : p ≠ 0 := (Polynomial.mem_roots'.1 h).1

