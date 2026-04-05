import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem sub_limZero {f g : CauSeq β abv} (hf : CauSeq.LimZero f) (hg : CauSeq.LimZero g) : CauSeq.LimZero (f - g) := by
  simpa only [sub_eq_add_neg] using CauSeq.add_limZero hf (CauSeq.neg_limZero hg)

