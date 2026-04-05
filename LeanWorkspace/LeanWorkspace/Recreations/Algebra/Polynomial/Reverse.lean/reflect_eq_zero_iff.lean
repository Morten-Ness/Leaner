import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

set_option backward.isDefEq.respectTransparency false in
theorem reflect_eq_zero_iff {N : ℕ} {f : R[X]} : Polynomial.reflect N (f : R[X]) = 0 ↔ f = 0 := by
  rw [ofFinsupp_eq_zero, Polynomial.reflect, embDomain_eq_zero, ofFinsupp_eq_zero]

