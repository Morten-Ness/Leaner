import Mathlib

variable {β G M : Type*}

variable [DivInvMonoid G] [Preorder G] [MulLeftMono G]

theorem one_lt_zpow {x : G} (hx : 1 < x) {n : ℤ} (hn : 0 < n) : 1 < x ^ n := by
  lift n to ℕ using Int.le_of_lt hn
  rw [zpow_natCast]
  exact one_lt_pow' hx (Int.natCast_pos.mp hn).ne'

