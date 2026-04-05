import Mathlib

variable {C : Type*} [Category* C] [Preadditive C]
  {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K L M : HomologicalComplex₂ C c₁ c₂) (φ : K ⟶ L) (e : K ≅ L) (ψ : L ⟶ M)
  (c₁₂ : ComplexShape I₁₂) [TotalComplexShape c₁ c₂ c₁₂]

variable [DecidableEq I₁₂] [K.HasTotal c₁₂]

theorem hom_ext {A : C} {i₁₂ : I₁₂} {f g : (K.total c₁₂).X i₁₂ ⟶ A}
    (h : ∀ (i₁ : I₁) (i₂ : I₂) (hi : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂),
      K.ιTotal c₁₂ i₁ i₂ i₁₂ hi ≫ f = K.ιTotal c₁₂ i₁ i₂ i₁₂ hi ≫ g) : f = g := by
  apply GradedObject.mapObj_ext
  rintro ⟨i₁, i₂⟩ hi
  exact h i₁ i₂ hi

