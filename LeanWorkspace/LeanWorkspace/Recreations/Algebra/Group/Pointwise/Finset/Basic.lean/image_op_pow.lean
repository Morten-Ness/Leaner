import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem image_op_pow (s : Finset α) : ∀ n : ℕ, (s ^ n).image op = s.image op ^ n
  | 0 => by simp [Finset.singleton_one]
  | n + 1 => by rw [pow_succ, pow_succ', Finset.image_op_mul, image_op_pow]
