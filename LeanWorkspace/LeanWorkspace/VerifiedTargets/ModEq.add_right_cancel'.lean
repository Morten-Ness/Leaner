import Mathlib

variable {M : Type*} [AddCancelCommMonoid M] {a b c d p : M}

theorem add_right_cancel' (c : M) : a + c ≡ b + c [PMOD p] → a ≡ b [PMOD p] := AddCommGroup.modEq_rfl.add_right_cancel

