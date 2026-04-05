import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : ℤ}

theorem Odd.zpow_pos_iff (hn : Odd n) : 0 < a ^ n ↔ 0 < a := lt_iff_lt_of_le_iff_le hn.zpow_nonpos_iff

alias ⟨_, Odd.zpow_neg⟩ := Odd.zpow_neg_iff

alias ⟨_, Odd.zpow_nonpos⟩ := Odd.zpow_nonpos_iff

