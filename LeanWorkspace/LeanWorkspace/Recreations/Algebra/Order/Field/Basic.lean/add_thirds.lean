import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

omit [PosMulReflectLT α] in
theorem add_thirds (a : α) : a / 3 + a / 3 + a / 3 = a := by
  rw [← add_div, ← add_div, ← two_mul, ← add_one_mul 2 a, two_add_one_eq_three,
    mul_div_cancel_left₀ a three_ne_zero]

