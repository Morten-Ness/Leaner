import Mathlib

variable {G : Type*}

variable [DivInvMonoid G]

theorem zpow_natCast (a : G) : ∀ n : ℕ, a ^ (n : ℤ) = a ^ n
  | 0 => (zpow_zero _).trans (pow_zero _).symm
  | n + 1 => calc
    a ^ (↑(n + 1) : ℤ) = a ^ (n : ℤ) * a := DivInvMonoid.zpow_succ' _ _
    _ = a ^ n * a := congrArg (· * a) (zpow_natCast a n)
    _ = a ^ (n + 1) := (pow_succ _ _).symm

