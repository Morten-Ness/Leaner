import Mathlib

variable (k : Type*) {V : Type*} (P : Type*) [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

variable {k P}

theorem ext_iff (s₁ s₂ : AffineSubspace k P) : s₁ = s₂ ↔ (s₁ : Set P) = s₂ := SetLike.ext'_iff

