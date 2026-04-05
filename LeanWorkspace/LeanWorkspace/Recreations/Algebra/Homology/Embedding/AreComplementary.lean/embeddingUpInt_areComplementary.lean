import Mathlib

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

theorem embeddingUpInt_areComplementary (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    AreComplementary (embeddingUpIntLE n₀) (embeddingUpIntGE n₁) where
  disjoint i₁ i₂ := by dsimp; lia
  union i := by
    by_cases hi : i ≤ n₀
    · obtain ⟨k, rfl⟩ := Int.exists_add_of_le hi
      exact Or.inl ⟨k, by dsimp; lia⟩
    · obtain ⟨k, rfl⟩ := Int.exists_add_of_le (show n₁ ≤ i by lia)
      exact Or.inr ⟨k, rfl⟩

