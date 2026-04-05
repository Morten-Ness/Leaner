import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem limZero_sub_rev {f g : CauSeq β abv} (hfg : CauSeq.LimZero (f - g)) : CauSeq.LimZero (g - f) := by
  simpa using CauSeq.neg_limZero hfg

