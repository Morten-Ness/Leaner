import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem mem_roots' : a ∈ p.roots ↔ p ≠ 0 ∧ IsRoot p a := by
  classical
  rw [← count_pos, Polynomial.count_roots p, rootMultiplicity_pos']

