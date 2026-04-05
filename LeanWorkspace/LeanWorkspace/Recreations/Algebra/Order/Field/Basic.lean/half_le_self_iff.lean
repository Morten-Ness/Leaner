import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

theorem half_le_self_iff : a / 2 ≤ a ↔ 0 ≤ a := by
  rw [div_le_iff₀ (zero_lt_two' α), mul_two, le_add_iff_nonneg_left]

