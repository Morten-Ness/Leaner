import Mathlib

variable {F α β : Type*}

variable [Semiring α] [Semiring β] {a b : α} {m n : ℕ}

theorem Even.pow_of_ne_zero (ha : Even a) : ∀ {n : ℕ}, n ≠ 0 → Even (a ^ n)
  | n + 1, _ => by rw [pow_succ]; exact ha.mul_left _
