import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {X₀ X₁ : C} (f : X₀ ⟶ X₁) {ι : Type*} {c : ComplexShape ι}
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁)

theorem double_d_eq_zero₁ (a b : ι) (hb : b ≠ i₁) :
    (HomologicalComplex.double f hi₀₁).d a b = 0 := dif_neg (by tauto)

