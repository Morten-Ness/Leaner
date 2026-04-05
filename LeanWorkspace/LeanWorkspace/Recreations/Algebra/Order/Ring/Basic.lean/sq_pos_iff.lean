import Mathlib

variable {α M R : Type*}

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] {a b : R} {m n : ℕ}

variable [ExistsAddOfLE R]

theorem sq_pos_iff {a : R} : 0 < a ^ 2 ↔ a ≠ 0 := even_two.pow_pos_iff two_ne_zero

alias ⟨_, sq_pos_of_ne_zero⟩ := sq_pos_iff
alias pow_two_pos_of_ne_zero := sq_pos_of_ne_zero

