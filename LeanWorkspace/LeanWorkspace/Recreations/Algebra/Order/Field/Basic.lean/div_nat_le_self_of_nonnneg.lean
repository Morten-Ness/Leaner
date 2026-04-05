import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

theorem div_nat_le_self_of_nonnneg (ha : 0 ≤ a) (n : ℕ) : a / n ≤ a := if h : n = 0 then by simpa [h] using ha
  else div_le_self ha (n.one_le_cast_iff_ne_zero.mpr h)

