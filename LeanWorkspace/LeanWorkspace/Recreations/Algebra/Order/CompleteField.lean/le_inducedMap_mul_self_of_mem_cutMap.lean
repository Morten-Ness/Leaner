import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable (α β γ) [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [Field β] [ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β]
  [Field γ] [ConditionallyCompleteLinearOrder γ] [IsStrictOrderedRing γ]

variable [Archimedean α]

variable {α β} {a : α} {b : β} {q : ℚ}

theorem le_inducedMap_mul_self_of_mem_cutMap (ha : 0 < a) (b : β) (hb : b ∈ LinearOrderedField.cutMap β (a * a)) :
    b ≤ ConditionallyCompleteLinearOrderedField.inducedMap α β a * ConditionallyCompleteLinearOrderedField.inducedMap α β a := by
  obtain ⟨q, hb, rfl⟩ := hb
  obtain ⟨q', hq', hqq', hqa⟩ := exists_rat_pow_btwn two_ne_zero hb (mul_self_pos.2 ha.ne')
  trans (q' : β) ^ 2
  · exact mod_cast hqq'.le
  · rw [pow_two] at hqa ⊢
    exact mul_self_le_mul_self (mod_cast hq'.le)
      (le_csSup (LinearOrderedField.cutMap_bddAbove β a) <|
        LinearOrderedField.coe_mem_cutMap_iff.2 <| lt_of_mul_self_lt_mul_self₀ ha.le hqa)

