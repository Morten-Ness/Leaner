import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [Preorder β] [MulLeftMono M] [MulRightMono M]

theorem pow_le_pow_left' {a b : M} (hab : a ≤ b) : ∀ i : ℕ, a ^ i ≤ b ^ i
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, pow_succ]
    exact mul_le_mul' (pow_le_pow_left' hab k) hab
