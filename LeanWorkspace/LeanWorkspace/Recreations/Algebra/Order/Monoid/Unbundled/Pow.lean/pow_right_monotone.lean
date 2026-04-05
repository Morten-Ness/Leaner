import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [Preorder M]

variable [MulLeftMono M] {a : M} {n : ℕ}

theorem pow_right_monotone (ha : 1 ≤ a) : Monotone fun n : ℕ ↦ a ^ n := monotone_nat_of_le_succ fun n ↦ by rw [pow_succ]; exact le_mul_of_one_le_right' ha

