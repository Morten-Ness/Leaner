FAIL
import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem self_modEq_zero : p ≡ 0 [PMOD p] := by
  change p ∣ p - 0
  simpa
