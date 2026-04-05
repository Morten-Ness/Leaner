import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

omit [PosMulReflectLT α] in
theorem sub_self_div_two (a : α) : a - a / 2 = a / 2 := by
  grind

