import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

variable [Ring β] {abv : β → α}

variable [IsAbsoluteValue abv]

theorem mul_equiv_zero' (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0) : f * g ≈ 0 := have : CauSeq.LimZero (f - 0) := hf
  have : CauSeq.LimZero (f * g) := CauSeq.mul_limZero_left _ <| by simpa
  show CauSeq.LimZero (f * g - 0) by simpa

