import Mathlib

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

variable (ac : AreComplementary e₁ e₂)

theorem fromSum_bijective : Function.Bijective (ComplexShape.Embedding.AreComplementary.fromSum e₁ e₂) := by
  constructor
  · rintro (i₁ | i₂) (j₁ | j₂) h
    · obtain rfl := e₁.injective_f h
      rfl
    · exact (ac.disjoint _ _ h).elim
    · exact (ac.disjoint _ _ ComplexShape.Embedding.AreComplementary.symm h).elim
    · obtain rfl := e₂.injective_f h
      rfl
  · intro n
    obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union n
    · exact ⟨Sum.inl i₁, rfl⟩
    · exact ⟨Sum.inr i₂, rfl⟩

