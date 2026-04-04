import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

theorem lt_iff_le_and_exists (s₁ s₂ : AffineSubspace k P) :
    s₁ < s₂ ↔ s₁ ≤ s₂ ∧ ∃ p ∈ s₂, p ∉ s₁ := by
  rw [lt_iff_le_not_ge, AffineSubspace.not_le_iff_exists]

