import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

theorem half_lt_self_iff : a / 2 < a ↔ 0 < a := by
  rw [div_lt_iff₀ (zero_lt_two' α), mul_two, lt_add_iff_pos_left]

alias ⟨_, half_le_self⟩ := half_le_self_iff

alias ⟨_, half_lt_self⟩ := half_lt_self_iff

alias div_two_lt_of_pos := half_lt_self

