import Mathlib

variable {R : Type u} {α : Type*}

variable [Semiring R] [LinearOrder R] {a b c : R}

theorem sq_nonpos_iff [ExistsAddOfLE R]
    [PosMulMono R] [AddLeftMono R] [NoZeroDivisors R] (r : R) :
    r ^ 2 ≤ 0 ↔ r = 0 := by
  trans r ^ 2 = 0
  · rw [le_antisymm_iff, and_iff_left (sq_nonneg r)]
  · exact sq_eq_zero_iff

alias pow_two_nonneg := sq_nonneg

