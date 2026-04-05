import Mathlib

variable {M : Type*} [CancelCommMonoid M] [LinearOrder M] [IsOrderedMonoid M] [LocallyFiniteOrder M]

theorem Finset.card_Ico_mul_right [ExistsMulOfLE M] (a b c : M) :
    #(Ico (a * c) (b * c)) = #(Ico a b) := by
  have : (Ico (a * c) (b * c)) = (Ico a b).map (mulRightEmbedding c) := by
    ext x
    simp only [mem_Ico, mem_map, mulRightEmbedding_apply]
    constructor
    · rintro ⟨h₁, h₂⟩
      obtain ⟨d, rfl⟩ := exists_mul_of_le h₁
      exact ⟨a * d, ⟨by simpa using h₁, by simpa [mul_right_comm a c d] using h₂⟩,
        by simp_rw [mul_assoc, mul_comm]⟩
    · aesop
  simp [this]

