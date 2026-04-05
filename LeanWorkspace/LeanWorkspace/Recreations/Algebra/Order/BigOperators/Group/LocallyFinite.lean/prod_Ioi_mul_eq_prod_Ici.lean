import Mathlib

variable {α M : Type*} [CommMonoid M] {f : α → M} {a b : α}

variable [PartialOrder α]

variable [LocallyFiniteOrderTop α]

theorem prod_Ioi_mul_eq_prod_Ici (a : α) : (∏ x ∈ Ioi a, f x) * f a = ∏ x ∈ Ici a, f x := by
  rw [mul_comm, Finset.mul_prod_Ioi_eq_prod_Ici]

