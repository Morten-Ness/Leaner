import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem not_limZero_of_not_congr_zero {f : CauSeq _ abv} (hf : ¬f ≈ 0) : ¬CauSeq.LimZero f := by
  intro h
  have : CauSeq.LimZero (f - 0) := by simp [h]
  exact hf this

