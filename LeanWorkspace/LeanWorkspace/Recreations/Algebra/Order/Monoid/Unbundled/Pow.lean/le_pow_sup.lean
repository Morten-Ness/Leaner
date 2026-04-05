import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [SemilatticeSup M] [MulLeftMono M] [MulRightMono M] {a b : M} {n : ℕ}

theorem le_pow_sup : a ^ n ⊔ b ^ n ≤ (a ⊔ b) ^ n := sup_le (pow_le_pow_left' le_sup_left _) (pow_le_pow_left' le_sup_right _)

