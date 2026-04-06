FAIL
import Mathlib

variable {G₀ : Type*}

variable [GroupWithZero G₀] {a b : G₀}

theorem zpow_self₀ (a : G₀) (n : ℤ) : Commute (a ^ n) a := by
  induction n with
  | ofNat m =>
      simpa using commute_self_zpow a m
  | negSucc m =>
      simpa using (commute_self a).inv_left.zpow_left (Int.ofNat (m + 1))
