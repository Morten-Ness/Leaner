import Mathlib

variable {A M : Type*} [AddGroup A] [DivisionMonoid M]

theorem map_neg_eq_inv (ψ : AddChar A M) (a : A) : ψ (-a) = (ψ a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simp only [← AddChar.map_add_eq_mul, neg_add_cancel, map_zero_eq_one]

