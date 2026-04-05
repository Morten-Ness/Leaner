import Mathlib

variable {G : Type*}

variable [DivInvMonoid G]

theorem zpow_ofNat (a : G) (n : ℕ) : a ^ (ofNat(n) : ℤ) = a ^ OfNat.ofNat n := zpow_natCast ..

