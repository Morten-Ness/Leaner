import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

theorem add_div_two_lt_right : (a + b) / 2 < b ↔ a < b := by simp [div_lt_iff₀, mul_two]

