import Mathlib

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {X₀ X₁ : C} (f : X₀ ⟶ X₁) {ι : Type*} {c : ComplexShape ι}
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁)

theorem to_double_hom_ext {K : HomologicalComplex C c} {φ φ' : K ⟶ HomologicalComplex.double f hi₀₁}
    (h₀ : φ.f i₀ = φ'.f i₀) (h₁ : φ.f i₁ = φ'.f i₁) : φ = φ' := by
  ext k
  by_cases h : k = i₀ ∨ k = i₁
  · obtain rfl | rfl := h <;> assumption
  · simp only [not_or] at h
    apply (HomologicalComplex.isZero_double_X f hi₀₁ k h.1 h.2).eq_of_tgt

