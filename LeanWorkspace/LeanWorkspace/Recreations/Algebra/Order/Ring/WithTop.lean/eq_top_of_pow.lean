import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] {x : WithTop α} {n : ℕ}

theorem eq_top_of_pow (n : ℕ) (hx : x ^ n = ⊤) : x = ⊤ := (pow_eq_top_iff.1 hx).1

