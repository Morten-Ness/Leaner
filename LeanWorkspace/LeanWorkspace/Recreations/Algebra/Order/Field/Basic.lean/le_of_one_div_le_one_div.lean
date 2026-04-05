import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

theorem le_of_one_div_le_one_div (ha : 0 < a) (h : 1 / a ≤ 1 / b) : b ≤ a := by
  simpa using one_div_le_one_div_of_le (by simpa) h

