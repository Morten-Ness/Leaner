import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {X₀ X₁ : C} (f : X₀ ⟶ X₁) {ι : Type*} {c : ComplexShape ι}
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁)

theorem isZero_double_X (k : ι) (h₀ : k ≠ i₀) (h₁ : k ≠ i₁) :
    IsZero ((HomologicalComplex.double f hi₀₁).X k) := by
  dsimp [HomologicalComplex.double]
  rw [if_neg h₀, if_neg h₁]
  exact Limits.isZero_zero C

