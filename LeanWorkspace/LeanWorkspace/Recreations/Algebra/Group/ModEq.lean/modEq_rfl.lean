import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem modEq_rfl : a ≡ a [PMOD p] := AddCommGroup.modEq_refl _

