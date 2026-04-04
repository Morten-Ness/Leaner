import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

theorem not_le_iff_exists (s₁ s₂ : AffineSubspace k P) : ¬s₁ ≤ s₂ ↔ ∃ p ∈ s₁, p ∉ s₂ := Set.not_subset

