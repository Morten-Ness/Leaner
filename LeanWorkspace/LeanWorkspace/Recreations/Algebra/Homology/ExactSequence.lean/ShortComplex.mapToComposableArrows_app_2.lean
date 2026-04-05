import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

theorem ShortComplex.mapToComposableArrows_app_2 {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    (CategoryTheory.ShortComplex.mapToComposableArrows φ).app 2 = φ.τ₃ := rfl

