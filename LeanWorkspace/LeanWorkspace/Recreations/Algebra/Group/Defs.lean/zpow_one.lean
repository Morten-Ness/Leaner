import Mathlib

variable {G : Type*}

variable [DivInvMonoid G]

theorem zpow_one (a : G) : a ^ (1 : ℤ) = a := by rw [zpow_ofNat, pow_one]

