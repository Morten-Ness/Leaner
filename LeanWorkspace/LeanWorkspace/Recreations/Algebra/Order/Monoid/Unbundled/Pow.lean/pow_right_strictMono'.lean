import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [MulLeftStrictMono M] {a : M} {n m : ℕ}

theorem pow_right_strictMono' (ha : 1 < a) : StrictMono ((a ^ ·) : ℕ → M) := strictMono_nat_of_lt_succ fun n ↦ by rw [pow_succ]; exact lt_mul_of_one_lt_right' (a ^ n) ha

