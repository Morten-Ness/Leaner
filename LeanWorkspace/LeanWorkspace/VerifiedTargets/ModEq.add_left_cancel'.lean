import Mathlib

variable {M : Type*} [AddCancelCommMonoid M] {a b c d p : M}

theorem add_left_cancel' (c : M) : c + a ≡ c + b [PMOD p] → a ≡ b [PMOD p] := AddCommGroup.modEq_rfl.add_left_cancel

