import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [MulLeftMono M] {a : M}

theorem pow_lt_one_of_lt {a : M} {n : ℕ} (h : a < 1) (hn : n ≠ 0) : a ^ n < 1 := by
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨k, rfl⟩
  rw [pow_succ']
  exact mul_lt_one_of_lt_of_le h (Left.pow_le_one_of_le h.le _)

