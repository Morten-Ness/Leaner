import Mathlib

variable {α M : Type*} [CommMonoid M] {f : α → M} {a b : α}

variable [PartialOrder α]

variable [LocallyFiniteOrderBot α]

theorem prod_Iio_mul_eq_prod_Iic (a : α) : (∏ x ∈ Iio a, f x) * f a = ∏ x ∈ Iic a, f x := by
  rw [mul_comm, Finset.mul_prod_Iio_eq_prod_Iic]

