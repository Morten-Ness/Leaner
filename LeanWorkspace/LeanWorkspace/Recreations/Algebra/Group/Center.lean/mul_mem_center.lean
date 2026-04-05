import Mathlib

variable {M : Type*} {S T : Set M}

variable [Mul M]

theorem mul_mem_center {z₁ z₂ : M} (hz₁ : z₁ ∈ Set.center M) (hz₂ : z₂ ∈ Set.center M) :
    z₁ * z₂ ∈ Set.center M := by
  simp only [commute_iff_eq, Set.mem_center_iff, isMulCentral_iff] at *
  grind

