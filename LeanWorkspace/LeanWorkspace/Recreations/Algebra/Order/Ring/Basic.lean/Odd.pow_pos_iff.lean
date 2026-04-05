import Mathlib

variable {α M R : Type*}

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {a b : R} {m n : ℕ}

variable [ExistsAddOfLE R]

theorem Odd.pow_pos_iff (hn : Odd n) : 0 < a ^ n ↔ 0 < a := lt_iff_lt_of_le_iff_le hn.pow_nonpos_iff

alias ⟨_, Odd.pow_nonpos⟩ := Odd.pow_nonpos_iff
alias ⟨_, Odd.pow_neg⟩ := Odd.pow_neg_iff

