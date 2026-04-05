import Mathlib

variable {M G : Type*}

variable [Monoid M]

variable [IsMulTorsionFree M] {n : ℕ} {a b : M}

theorem pow_left_inj (hn : n ≠ 0) : a ^ n = b ^ n ↔ a = b := (pow_left_injective hn).eq_iff

