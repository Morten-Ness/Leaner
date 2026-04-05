import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [DivisionMonoid α] {s t : Finset α} {n : ℤ}

theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1 := by
  simp_rw [← coe_inj, Finset.coe_mul, Finset.coe_one, Set.mul_eq_one_iff, coe_singleton]

