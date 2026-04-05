import Mathlib

variable {α M : Type*} [CommMonoid M] {f : α → M} {a b : α}

variable [PartialOrder α]

variable [LocallyFiniteOrder α]

theorem mul_prod_Ioo_eq_prod_Ioc (h : a < b) : f b * ∏ x ∈ Ioo a b, f x = ∏ x ∈ Ioc a b, f x := by
  rw [Ioc_eq_cons_Ioo h, prod_cons]

