import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable (α β γ) [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [Field β] [ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β]
  [Field γ] [ConditionallyCompleteLinearOrder γ] [IsStrictOrderedRing γ]

variable [Archimedean α]

variable {α β} {a : α} {b : β} {q : ℚ}

theorem exists_mem_cutMap_mul_self_of_lt_inducedMap_mul_self (ha : 0 < a) (b : β)
    (hba : b < ConditionallyCompleteLinearOrderedField.inducedMap α β a * ConditionallyCompleteLinearOrderedField.inducedMap α β a) : ∃ c ∈ LinearOrderedField.cutMap β (a * a), b < c := by
  obtain hb | hb := lt_or_ge b 0
  · refine ⟨0, ?_, hb⟩
    rw [← Rat.cast_zero, LinearOrderedField.coe_mem_cutMap_iff, Rat.cast_zero]
    exact mul_self_pos.2 ha.ne'
  obtain ⟨q, hq, hbq, hqa⟩ := exists_rat_pow_btwn two_ne_zero hba (hb.trans_lt hba)
  rw [← cast_pow] at hbq
  refine ⟨(q ^ 2 : ℚ), LinearOrderedField.coe_mem_cutMap_iff.2 ?_, hbq⟩
  rw [pow_two] at hqa ⊢
  push_cast
  obtain ⟨q', hq', hqa'⟩ := ConditionallyCompleteLinearOrderedField.lt_inducedMap_iff.1 (lt_of_mul_self_lt_mul_self₀
    (ConditionallyCompleteLinearOrderedField.inducedMap_nonneg ha.le) hqa)
  exact mul_self_lt_mul_self (mod_cast hq.le) (hqa'.trans' <| by assumption_mod_cast)

