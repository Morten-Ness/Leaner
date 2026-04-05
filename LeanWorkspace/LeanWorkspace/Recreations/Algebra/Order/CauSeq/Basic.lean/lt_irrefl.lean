import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem lt_irrefl {f : CauSeq α abs} : ¬f < f
  | h => CauSeq.not_limZero_of_pos h (by simp [CauSeq.zero_limZero])
