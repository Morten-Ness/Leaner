import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem mem_roots_sub_C' {p : R[X]} {a x : R} : x ∈ (p - C a).roots ↔ p ≠ C a ∧ p.eval x = a := by
  rw [Polynomial.mem_roots', IsRoot.def, sub_ne_zero, eval_sub, sub_eq_zero, eval_C]

