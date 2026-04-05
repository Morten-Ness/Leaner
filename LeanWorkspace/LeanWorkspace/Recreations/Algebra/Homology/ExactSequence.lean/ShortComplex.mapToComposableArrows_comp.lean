import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

theorem ShortComplex.mapToComposableArrows_comp {S₁ S₂ S₃ : ShortComplex C} (φ : S₁ ⟶ S₂)
    (ψ : S₂ ⟶ S₃) : CategoryTheory.ShortComplex.mapToComposableArrows (φ ≫ ψ) =
      CategoryTheory.ShortComplex.mapToComposableArrows φ ≫ CategoryTheory.ShortComplex.mapToComposableArrows ψ := by
  cat_disch

