import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem isMonicOfDegree_zero_iff {p : R[X]} : IsMonicOfDegree p 0 ↔ p = 1 := by
  simp only [isMonicOfDegree_iff']
  refine ⟨fun ⟨H₁, H₂⟩ ↦ eq_one_of_monic_natDegree_zero H₂ H₁, fun H ↦ ?_⟩
  subst H
  simp

