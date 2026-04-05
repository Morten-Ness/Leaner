import Mathlib

variable {A M : Type*} [AddCommGroup A] [DivisionCommMonoid M]

theorem sub_apply' (ψ χ : AddChar A M) (a : A) : (ψ - χ) a = ψ a / χ a := by
  rw [AddChar.sub_apply, AddChar.map_neg_eq_inv, div_eq_mul_inv]

