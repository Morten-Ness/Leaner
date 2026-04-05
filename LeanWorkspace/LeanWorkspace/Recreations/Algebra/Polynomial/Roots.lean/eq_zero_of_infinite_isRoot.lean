import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem eq_zero_of_infinite_isRoot (p : R[X]) (h : Set.Infinite { x | IsRoot p x }) : p = 0 := not_imp_comm.mp Polynomial.finite_setOf_isRoot h

