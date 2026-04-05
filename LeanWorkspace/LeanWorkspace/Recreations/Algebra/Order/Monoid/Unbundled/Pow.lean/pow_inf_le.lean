import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [SemilatticeInf M] [MulLeftMono M] [MulRightMono M] {a b : M} {n : ℕ}

theorem pow_inf_le : (a ⊓ b) ^ n ≤ a ^ n ⊓ b ^ n := le_inf (pow_le_pow_left' inf_le_left _) (pow_le_pow_left' inf_le_right _)

