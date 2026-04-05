import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

omit [PosMulReflectLT α] in
theorem div_two_sub_self (a : α) : a / 2 - a = -(a / 2) := by
  grind

