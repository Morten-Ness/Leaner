import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {X₀ X₁ : C} (f : X₀ ⟶ X₁) {ι : Type*} {c : ComplexShape ι}
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁)

theorem double_d (h : i₀ ≠ i₁) :
    (HomologicalComplex.double f hi₀₁).d i₀ i₁ =
      (HomologicalComplex.doubleXIso₀ f hi₀₁).hom ≫ f ≫ (HomologicalComplex.doubleXIso₁ f hi₀₁ h).inv := dif_pos ⟨rfl, rfl, h⟩

