import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem modEq_zero : a ≡ b [PMOD 0] ↔ a = b := by simp [AddCommGroup.modEq_iff_nsmul]

