import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

theorem one_le_div (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a := by rw [le_div_iff₀ hb, one_mul]

