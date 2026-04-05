import Mathlib

variable {α M : Type*} [CommMonoid M] {f : α → M} {a b : α}

variable [PartialOrder α]

variable [LocallyFiniteOrderBot α]

theorem mul_prod_Iio_eq_prod_Iic (a : α) : f a * ∏ x ∈ Iio a, f x = ∏ x ∈ Iic a, f x := by
  rw [Iic_eq_cons_Iio, prod_cons]

