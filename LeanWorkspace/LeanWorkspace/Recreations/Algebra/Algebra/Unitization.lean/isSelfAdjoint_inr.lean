import Mathlib

variable {R A : Type*} [Semiring R]

variable [StarAddMonoid R] [Star A] {a : A}

theorem isSelfAdjoint_inr : IsSelfAdjoint (a : Unitization R A) ↔ IsSelfAdjoint a := by
  simp only [isSelfAdjoint_iff, ← Unitization.inr_star, Unitization.inr_injective.eq_iff]

alias ⟨_root_.IsSelfAdjoint.of_inr, _⟩ := isSelfAdjoint_inr

