import Mathlib

variable {β G M : Type*}

variable [DivInvMonoid G] [Preorder G] [MulLeftMono G]

theorem one_le_zpow {x : G} (H : 1 ≤ x) {n : ℤ} (hn : 0 ≤ n) : 1 ≤ x ^ n := by
  lift n to ℕ using hn
  rw [zpow_natCast]
  apply one_le_pow_of_one_le' H

