import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

theorem ShortComplex.mapToComposableArrows_id {S₁ : ShortComplex C} :
    (CategoryTheory.ShortComplex.mapToComposableArrows (𝟙 S₁)) = 𝟙 S₁.toComposableArrows := by
  cat_disch

