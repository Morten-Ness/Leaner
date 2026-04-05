import Mathlib

theorem le_self_sq (b : ℤ) : b ≤ b ^ 2 := le_trans le_natAbs (Int.natAbs_le_self_sq _)

alias le_self_pow_two := le_self_sq

