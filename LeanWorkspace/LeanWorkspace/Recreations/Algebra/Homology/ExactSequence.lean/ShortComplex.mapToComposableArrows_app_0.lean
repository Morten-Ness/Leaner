import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

theorem ShortComplex.mapToComposableArrows_app_0 {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) :
    (CategoryTheory.ShortComplex.mapToComposableArrows φ).app 0 = φ.τ₁ := rfl

