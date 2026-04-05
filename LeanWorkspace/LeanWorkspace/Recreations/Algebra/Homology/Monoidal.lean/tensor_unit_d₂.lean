import Mathlib

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [HasZeroObject C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns]

variable (K : HomologicalComplex C c) [DecidableEq I]

variable [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]

theorem tensor_unit_d₂ (i₁ i₂ j : I) :
    mapBifunctor.d₂ K (tensorUnit C c) (curriedTensor C) c i₁ i₂ j = 0 := by
  by_cases h₁ : c.Rel i₂ (c.next i₂)
  · by_cases h₂ : ComplexShape.π c c c (i₁, c.next i₂) = j
    · rw [mapBifunctor.d₂_eq _ _ _ _ _ h₁ _ h₂, single_obj_d, Functor.map_zero,
        zero_comp, smul_zero]
    · rw [mapBifunctor.d₂_eq_zero' _ _ _ _ _ h₁ _ h₂]
  · rw [mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ h₁]

