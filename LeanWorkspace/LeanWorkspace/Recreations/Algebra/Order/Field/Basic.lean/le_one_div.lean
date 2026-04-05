import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

theorem le_one_div (ha : 0 < a) (hb : 0 < b) : a ≤ 1 / b ↔ b ≤ 1 / a := by
  simpa using le_inv_comm₀ ha hb

