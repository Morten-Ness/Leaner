import Mathlib

variable (S : ShortComplex Ab.{u})

theorem ab_exact_iff_function_exact :
    S.Exact ↔ Function.Exact S.f S.g := by
  rw [S.ab_exact_iff]
  apply forall_congr'
  intro x₂
  constructor
  · intro h
    refine ⟨h, ?_⟩
    rintro ⟨x₁, rfl⟩
    simp only [CategoryTheory.ShortComplex.ab_zero_apply]
  · tauto

