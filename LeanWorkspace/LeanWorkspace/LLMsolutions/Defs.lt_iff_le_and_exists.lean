import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AddTorsor V P] {ι : Sort*}

theorem lt_iff_le_and_exists (s₁ s₂ : AffineSubspace k P) :
    s₁ < s₂ ↔ s₁ ≤ s₂ ∧ ∃ p ∈ s₂, p ∉ s₁ := by
  constructor
  · intro h
    refine ⟨le_of_lt h, ?_⟩
    by_contra h'
    apply ne_of_lt h
    ext p
    constructor
    · intro hp
      exact (le_of_lt h) hp
    · intro hp
      by_contra hp'
      exact h' ⟨p, hp, hp'⟩
  · rintro ⟨h₁₂, p, hp₂, hp₁⟩
    exact lt_of_le_of_ne h₁₂ (by
      intro hEq
      exact hp₁ (hEq ▸ hp₂))
