import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [MulLeftMono M] {a : M} {n : ℕ}

theorem le_self_pow (ha : 1 ≤ a) (hn : n ≠ 0) : a ≤ a ^ n := by
  simpa using pow_le_pow_right' ha (Nat.one_le_iff_ne_zero.2 hn)

