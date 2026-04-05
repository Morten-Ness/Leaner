import Mathlib

variable {C : Type*} [Category* C] [MonoidalCategory C] [Preadditive C] [HasZeroObject C]
  [(curriedTensor C).Additive] [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
  {I : Type*} [AddMonoid I] {c : ComplexShape I} [c.TensorSigns]

variable (K : HomologicalComplex C c) [DecidableEq I]

variable [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]

theorem unit_tensor_d₁ (i₁ i₂ j : I) :
    mapBifunctor.d₁ (tensorUnit C c) K (curriedTensor C) c i₁ i₂ j = 0 := by
  by_cases h₁ : c.Rel i₁ (c.next i₁)
  · by_cases h₂ : ComplexShape.π c c c (c.next i₁, i₂) = j
    · rw [mapBifunctor.d₁_eq _ _ _ _ h₁ _ _ h₂, single_obj_d, Functor.map_zero,
        zero_app, zero_comp, smul_zero]
    · rw [mapBifunctor.d₁_eq_zero' _ _ _ _ h₁ _ _ h₂]
  · rw [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ h₁]

