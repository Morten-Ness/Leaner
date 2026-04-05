import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

theorem div_le_self (ha : 0 ≤ a) (hb : 1 ≤ b) : a / b ≤ a := by
  simpa only [div_one] using div_le_div_of_nonneg_left ha zero_lt_one hb

