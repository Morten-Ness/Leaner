import Mathlib

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable {X : ι → Type*} (x₁ : ∀ i₁, X (e₁.f i₁)) (x₂ : ∀ i₂, X (e₂.f i₂))

theorem desc'_inr (i : ι₁ ⊕ ι₂) (i₂ : ι₂) (h : Sum.inr i₂ = i) :
    ac.desc' x₁ x₂ i = ComplexShape.Embedding.AreComplementary.desc.aux _ _ _ (by subst h; simp) (x₂ i₂) := by subst h; rfl

