import Mathlib

open scoped ArithmeticFunction

theorem finMulAntidiag_zero_left {n : ℕ} (hn : n ≠ 1) :
    Nat.finMulAntidiag 0 n = ∅ := by
  ext
  simp [hn.symm]

