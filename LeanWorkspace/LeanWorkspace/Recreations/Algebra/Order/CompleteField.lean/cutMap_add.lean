import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [Field α] [LinearOrder α]

variable (β) [IsStrictOrderedRing α] [Field β] [LinearOrder β] [IsStrictOrderedRing β]
  {a a₁ a₂ : α} {b : β} {q : ℚ}

variable [Archimedean α]

theorem cutMap_add (a b : α) : LinearOrderedField.cutMap β (a + b) = LinearOrderedField.cutMap β a + LinearOrderedField.cutMap β b := by
  refine (image_subset_iff.2 fun q hq => ?_).antisymm ?_
  · rw [mem_setOf_eq, ← sub_lt_iff_lt_add] at hq
    obtain ⟨q₁, hq₁q, hq₁ab⟩ := exists_rat_btwn hq
    refine ⟨q₁, by rwa [LinearOrderedField.coe_mem_cutMap_iff], q - q₁, ?_, add_sub_cancel _ _⟩
    norm_cast
    rw [LinearOrderedField.coe_mem_cutMap_iff]
    exact mod_cast sub_lt_comm.mp hq₁q
  · rintro _ ⟨_, ⟨qa, ha, rfl⟩, _, ⟨qb, hb, rfl⟩, rfl⟩
    -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
    refine ⟨qa + qb, ?_, by beta_reduce; norm_cast⟩
    rw [mem_setOf_eq, cast_add]
    exact add_lt_add ha hb

