import Mathlib

variable {M : Type*} [AddCancelCommMonoid M] {a b c d p : M}

theorem add_modEq_right : a + b ≡ b [PMOD p] ↔ a ≡ 0 [PMOD p] := by simp [add_comm a]

