import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

theorem le_def' (s₁ s₂ : AffineSubspace k P) : s₁ ≤ s₂ ↔ ∀ p ∈ s₁, p ∈ s₂ := Iff.rfl

