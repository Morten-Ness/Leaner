import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

theorem one_div_pow_le_one_div_pow_of_le (a1 : 1 ≤ a) {m n : ℕ} (mn : m ≤ n) :
    1 / a ^ n ≤ 1 / a ^ m := by
  refine (one_div_le_one_div ?_ ?_).mpr (pow_right_mono₀ a1 mn) <;>
    exact pow_pos (zero_lt_one.trans_le a1) _

