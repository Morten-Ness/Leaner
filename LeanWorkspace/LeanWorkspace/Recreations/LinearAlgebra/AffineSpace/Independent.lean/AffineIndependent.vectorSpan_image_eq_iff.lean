import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

theorem AffineIndependent.vectorSpan_image_eq_iff [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) {s₁ s₂ : Set ι} :
    vectorSpan k (p '' s₁) = vectorSpan k (p '' s₂) ↔
      s₁ = s₂ ∨ s₁.Subsingleton ∧ s₂.Subsingleton := by
  constructor
  · intro h
    by_cases he : s₁ = s₂
    · simp [he]
    simp only [he, false_or]
    by_cases h₁ : s₁.Subsingleton
    · rw [vectorSpan_of_subsingleton _ (h₁.image _), eq_comm, vectorSpan_eq_bot_iff_subsingleton]
        at h
      exact ⟨h₁, Set.subsingleton_of_image ha.injective s₂ h⟩
    by_cases h₂ : s₂.Subsingleton
    · rw [vectorSpan_of_subsingleton _ (h₂.image _), vectorSpan_eq_bot_iff_subsingleton]
        at h
      exact ⟨Set.subsingleton_of_image ha.injective s₁ h, h₂⟩
    simp only [h₁, h₂, false_and]
    have hi : (∃ i ∈ s₁, i ∉ s₂) ∨ ∃ i ∈ s₂, i ∉ s₁ := by grind
    rcases hi with ⟨i, his₁, his₂⟩ | ⟨i, his₂, his₁⟩
    · exact ha.vectorSpan_image_ne_of_mem_of_notMem_of_not_subsingleton his₁ his₂ h₁ h
    · exact ha.vectorSpan_image_ne_of_mem_of_notMem_of_not_subsingleton his₂ his₁ h₂ h.symm
  · intro h
    rcases h with rfl | ⟨h₁, h₂⟩
    · rfl
    · simp [h₁.image p, h₂.image p, vectorSpan_of_subsingleton]

