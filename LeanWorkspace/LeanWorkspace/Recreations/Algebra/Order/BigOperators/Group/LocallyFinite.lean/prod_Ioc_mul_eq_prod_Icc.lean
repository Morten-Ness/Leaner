import Mathlib

variable {α M : Type*} [CommMonoid M] {f : α → M} {a b : α}

variable [PartialOrder α]

variable [LocallyFiniteOrder α]

theorem prod_Ioc_mul_eq_prod_Icc (h : a ≤ b) : (∏ x ∈ Ioc a b, f x) * f a = ∏ x ∈ Icc a b, f x := by
  rw [mul_comm, Finset.mul_prod_Ioc_eq_prod_Icc h]

