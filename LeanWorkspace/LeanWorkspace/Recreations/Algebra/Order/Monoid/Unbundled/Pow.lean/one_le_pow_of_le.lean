import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [MulLeftMono M] {a : M}

theorem one_le_pow_of_le (ha : 1 ≤ a) : ∀ n : ℕ, 1 ≤ a ^ n
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ]
    exact one_le_mul (one_le_pow_of_le ha k) ha
