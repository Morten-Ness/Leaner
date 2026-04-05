import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [MulRightMono M] {x : M}

theorem Right.pow_lt_one_of_lt {n : ℕ} {x : M} (hn : 0 < n) (h : x < 1) : x ^ n < 1 := by
  rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨k, rfl⟩
  rw [pow_succ]
  exact mul_lt_one_of_le_of_lt (Left.pow_le_one_of_le h.le) h

