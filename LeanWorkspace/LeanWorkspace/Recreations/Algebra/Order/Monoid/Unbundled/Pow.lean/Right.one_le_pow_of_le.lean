import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [MulRightMono M] {x : M}

theorem Right.one_le_pow_of_le (hx : 1 ≤ x) : ∀ {n : ℕ}, 1 ≤ x ^ n
  | 0 => (pow_zero _).ge
  | n + 1 => by
    rw [pow_succ]
    exact Right.one_le_mul (Right.one_le_pow_of_le hx) hx
