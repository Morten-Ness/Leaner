import Mathlib

variable {M G : Type*}

variable [Monoid M]

variable [IsMulTorsionFree M] {n : ℕ} {a b : M}

theorem sq_eq_one : a ^ 2 = 1 ↔ a = 1 := pow_eq_one_iff_left (by lia)

