import Mathlib

variable {M : Type*} [AddCommMonoid M] {a b c d p : M}

theorem modEq_iff_nsmul : a ≡ b [PMOD p] ↔ ∃ m n : ℕ, m • p + a = n • p + b := by
  rfl

