import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [LinearOrder M]

variable [MulLeftMono M]

theorem one_le_pow_iff {x : M} {n : ℕ} (hn : n ≠ 0) : 1 ≤ x ^ n ↔ 1 ≤ x := ⟨le_imp_le_of_lt_imp_lt fun h => pow_lt_one' h hn, fun h => one_le_pow_of_one_le' h n⟩

