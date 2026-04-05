import Mathlib

variable {C D : Type*} [Category* C] [Category* D]

variable [Preadditive C] [Preadditive D] (S : ShortComplex C)

variable [Balanced C]

theorem epi_τ₂_of_exact_of_epi {S₁ S₂ : CategoryTheory.ShortComplex C} (φ : S₁ ⟶ S₂)
    (h₂ : S₂.Exact) [Epi S₁.g] [Epi S₂.g] [Epi φ.τ₁] [Epi φ.τ₃] : Epi φ.τ₂ := by
  have : Mono S₁.op.f := by dsimp; infer_instance
  have : Mono S₂.op.f := by dsimp; infer_instance
  have : Mono (opMap φ).τ₁ := by dsimp; infer_instance
  have : Mono (opMap φ).τ₃ := by dsimp; infer_instance
  have := CategoryTheory.ShortComplex.mono_τ₂_of_exact_of_mono (opMap φ) h₂.op
  exact unop_epi_of_mono (opMap φ).τ₂

