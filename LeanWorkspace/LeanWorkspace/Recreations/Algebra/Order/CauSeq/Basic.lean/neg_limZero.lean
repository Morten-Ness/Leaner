import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem neg_limZero {f : CauSeq β abv} (hf : CauSeq.LimZero f) : CauSeq.LimZero (-f) := by
  rw [← neg_one_mul f]
  exact CauSeq.mul_limZero_right _ hf

