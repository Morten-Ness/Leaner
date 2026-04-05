import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

omit [IsStrictOrderedRing α] in
theorem monotone_div_right_of_nonneg (ha : 0 ≤ a) : Monotone (· / a) := fun _b _c hbc ↦ div_le_div_of_nonneg_right hbc ha

