import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MonoidWithZero α] [NoZeroDivisors α] [Nontrivial α] {x : WithTop α} {n : ℕ}

theorem pow_ne_top (hx : x ≠ ⊤) : x ^ n ≠ ⊤ := WithTop.pow_ne_top_iff.2 <| .inl hx

