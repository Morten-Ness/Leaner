import Mathlib

variable {α M : Type*} [CommMonoid M] {f : α → M} {a b : α}

variable [PartialOrder α]

variable [LocallyFiniteOrder α]

theorem mul_prod_Ioc_eq_prod_Icc (h : a ≤ b) : f a * ∏ x ∈ Ioc a b, f x = ∏ x ∈ Icc a b, f x := by
  rw [Icc_eq_cons_Ioc h, prod_cons]

