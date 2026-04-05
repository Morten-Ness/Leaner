import Mathlib

variable {α β G M : Type*}

variable [Monoid M] {a b : M} {m n : ℕ}

theorem mul_pow_sub_one (hn : n ≠ 0) (a : M) : a * a ^ (n - 1) = a ^ n := by
  rw [← pow_succ', Nat.sub_add_cancel <| Nat.one_le_iff_ne_zero.2 hn]

