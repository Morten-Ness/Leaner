import Mathlib

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

variable {X : ι → Type*} (x₁ : ∀ i₁, X (e₁.f i₁)) (x₂ : ∀ i₂, X (e₂.f i₂))

theorem desc_inl (i₁ : ι₁) : ac.desc x₁ x₂ (e₁.f i₁) = x₁ i₁ := by
  dsimp [ComplexShape.Embedding.AreComplementary.desc]
  rw [ComplexShape.Embedding.AreComplementary.desc'_inl ac _ _ _ i₁ (ac.equiv.injective (by simp)), ComplexShape.Embedding.AreComplementary.desc.aux_trans]
  rfl

