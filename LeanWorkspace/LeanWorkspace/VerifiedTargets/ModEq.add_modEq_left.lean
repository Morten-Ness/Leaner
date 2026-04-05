import Mathlib

variable {M : Type*} [AddCancelCommMonoid M] {a b c d p : M}

theorem add_modEq_left : a + b ≡ a [PMOD p] ↔ b ≡ 0 [PMOD p] := by
  simpa using AddCommGroup.ModEq.add_iff_left (AddCommGroup.modEq_refl a) (d := 0)

