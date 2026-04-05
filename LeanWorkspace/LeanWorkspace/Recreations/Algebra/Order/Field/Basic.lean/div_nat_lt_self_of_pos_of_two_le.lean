import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

theorem div_nat_lt_self_of_pos_of_two_le (ha : 0 < a) {n : ℕ} (hn : 2 ≤ n) : a / n < a := div_lt_self ha (n.one_lt_cast.mpr hn)

