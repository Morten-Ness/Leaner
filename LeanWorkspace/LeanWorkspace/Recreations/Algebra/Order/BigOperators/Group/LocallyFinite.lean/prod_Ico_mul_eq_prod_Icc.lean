import Mathlib

variable {α M : Type*} [CommMonoid M] {f : α → M} {a b : α}

variable [PartialOrder α]

variable [LocallyFiniteOrder α]

theorem prod_Ico_mul_eq_prod_Icc (h : a ≤ b) : (∏ x ∈ Ico a b, f x) * f b = ∏ x ∈ Icc a b, f x := by
  rw [mul_comm, Finset.mul_prod_Ico_eq_prod_Icc h]

