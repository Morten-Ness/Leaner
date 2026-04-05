import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem inv_nonpos' : a⁻¹ ≤ 0 ↔ a ≤ 0 := by
  grind [inv_lt_zero', le_iff_eq_or_lt]

