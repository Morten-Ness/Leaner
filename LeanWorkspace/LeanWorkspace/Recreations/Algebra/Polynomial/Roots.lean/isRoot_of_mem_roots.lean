import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem isRoot_of_mem_roots (h : a ∈ p.roots) : IsRoot p a := (Polynomial.mem_roots'.1 h).2

