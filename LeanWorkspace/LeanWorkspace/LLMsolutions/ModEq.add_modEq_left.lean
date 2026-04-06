import Mathlib

variable {M : Type*} [AddCancelCommMonoid M] {a b c d p : M}

theorem add_modEq_left : a + b ≡ a [PMOD p] ↔ b ≡ 0 [PMOD p] := by
  simpa using (modEq_add_fac_left (a := b) (b := 0) (c := a) (n := p))
