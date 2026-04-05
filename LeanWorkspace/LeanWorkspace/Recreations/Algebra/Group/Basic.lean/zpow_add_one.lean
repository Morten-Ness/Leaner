import Mathlib

variable {α β G M : Type*}

variable [Group G] {a b c d : G} {n : ℤ}

theorem zpow_add_one (a : G) : ∀ n : ℤ, a ^ (n + 1) = a ^ n * a
  | (n : ℕ) => by simp only [← Int.natCast_succ, zpow_natCast, pow_succ]
  | -1 => by simp [Int.add_left_neg]
  | .negSucc (n + 1) => by
    rw [zpow_negSucc, pow_succ', mul_inv_rev, inv_mul_cancel_right]
    rw [Int.negSucc_eq, Int.neg_add, Int.neg_add_cancel_right]
    exact zpow_negSucc _ _
