import Mathlib

variable {A M : Type*} [AddCommGroup A] [DivisionCommMonoid M]

theorem inv_apply' (ψ : AddChar A M) (a : A) : ψ⁻¹ a = (ψ a)⁻¹ := by rw [inv_apply, AddChar.map_neg_eq_inv]

