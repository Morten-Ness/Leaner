import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem trichotomy (f : CauSeq α abs) : CauSeq.Pos f ∨ CauSeq.LimZero f ∨ CauSeq.Pos (-f) := by
  rcases Classical.em (CauSeq.LimZero f) with h | h
  · simp [*]
  simp only [false_or, h]
  rcases CauSeq.abv_pos_of_not_limZero h with ⟨K, K0, hK⟩
  rcases exists_forall_ge_and hK (CauSeq.cauchy₃ f K0) with ⟨i, hi⟩
  refine (le_total 0 (f i)).imp ?_ ?_ <;>
    refine fun h => ⟨K, K0, i, fun j ij => ?_⟩ <;>
    have := (hi _ ij).1 <;>
    obtain ⟨h₁, h₂⟩ := hi _ le_rfl
  · rwa [abs_of_nonneg] at this
    rw [abs_of_nonneg h] at h₁
    exact
      (le_add_iff_nonneg_right _).1
        (le_trans h₁ <| neg_le_sub_iff_le_add'.1 <| le_of_lt (abs_lt.1 <| h₂ _ ij).1)
  · rwa [abs_of_nonpos] at this
    rw [abs_of_nonpos h] at h₁
    rw [← sub_le_sub_iff_right, zero_sub]
    exact le_trans (le_of_lt (abs_lt.1 <| h₂ _ ij).2) h₁

