FAIL
import Mathlib

variable {A M : Type*} [AddCommGroup A] [DivisionCommMonoid M]

theorem div_apply' (ψ χ : AddChar A M) (a : A) : (ψ / χ) a = ψ a / χ a := by
  rw [div_eq_mul_inv, AddChar.inv_apply, inv_eq_iff_mul_eq, mul_comm, inv_mul_cancel]
