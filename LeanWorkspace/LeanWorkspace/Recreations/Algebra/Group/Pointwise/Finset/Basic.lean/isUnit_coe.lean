import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [DivisionMonoid α] {s t : Finset α} {n : ℤ}

theorem isUnit_coe : IsUnit (s : Set α) ↔ IsUnit s := by
  simp_rw [Finset.isUnit_iff, Set.isUnit_iff, coe_eq_singleton]

