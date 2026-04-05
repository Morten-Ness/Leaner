import Mathlib

variable {M G : Type*}

variable [Monoid M]

variable [IsMulTorsionFree M] {n : ℕ} {a b : M}

theorem pow_eq_one_iff_left (hn : n ≠ 0) : a ^ n = 1 ↔ a = 1 := by
  rw [← pow_left_inj (a := a) hn, one_pow]

-- We want to use `IsAddTorsion.nsmul_eq_zero_iff` earlier than `smul_eq_zero`.

