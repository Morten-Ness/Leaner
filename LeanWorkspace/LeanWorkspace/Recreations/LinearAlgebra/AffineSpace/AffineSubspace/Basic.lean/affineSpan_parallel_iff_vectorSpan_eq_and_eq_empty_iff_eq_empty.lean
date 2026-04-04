import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

theorem affineSpan_parallel_iff_vectorSpan_eq_and_eq_empty_iff_eq_empty {s₁ s₂ : Set P} :
    affineSpan k s₁ ∥ affineSpan k s₂ ↔ vectorSpan k s₁ = vectorSpan k s₂ ∧ (s₁ = ∅ ↔ s₂ = ∅) := by
  repeat rw [← direction_affineSpan, ← affineSpan_eq_bot k]
  exact AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot

