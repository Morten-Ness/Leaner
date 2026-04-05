import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] {x : WithTop α} {n : ℕ}

theorem pow_lt_top [Preorder α] (hx : x < ⊤) : x ^ n < ⊤ := pow_lt_top_iff.2 <| .inl hx

