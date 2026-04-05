FAIL
import Mathlib

variable {A M : Type*} [AddCommGroup A] [DivisionCommMonoid M]

theorem sub_apply' (ψ χ : AddChar A M) (a : A) : (ψ - χ) a = ψ a / χ a := by
  rw [sub_eq_add_neg, AddChar.add_apply, AddChar.neg_apply, div_eq_mul_inv]
