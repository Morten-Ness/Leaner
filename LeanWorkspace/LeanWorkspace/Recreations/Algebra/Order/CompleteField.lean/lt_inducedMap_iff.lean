import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable (α β γ) [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [Field β] [ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β]
  [Field γ] [ConditionallyCompleteLinearOrder γ] [IsStrictOrderedRing γ]

variable [Archimedean α]

variable {α β} {a : α} {b : β} {q : ℚ}

theorem lt_inducedMap_iff : b < ConditionallyCompleteLinearOrderedField.inducedMap α β a ↔ ∃ q : ℚ, b < q ∧ (q : α) < a := ⟨fun h => (exists_rat_btwn h).imp fun _ => And.imp_right ConditionallyCompleteLinearOrderedField.coe_lt_inducedMap_iff.1,
    fun ⟨q, hbq, hqa⟩ => hbq.trans <| by rwa [ConditionallyCompleteLinearOrderedField.coe_lt_inducedMap_iff]⟩

