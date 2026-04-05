import Mathlib

variable {A M : Type*} [AddCommGroup A] [DivisionCommMonoid M]

theorem neg_apply' (ψ : AddChar A M) (a : A) : (-ψ) a = (ψ a)⁻¹ := AddChar.map_neg_eq_inv _ _

