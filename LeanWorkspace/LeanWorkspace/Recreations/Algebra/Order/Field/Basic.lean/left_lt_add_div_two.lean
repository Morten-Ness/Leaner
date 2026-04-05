import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

theorem left_lt_add_div_two : a < (a + b) / 2 ↔ a < b := by simp [lt_div_iff₀, mul_two]

