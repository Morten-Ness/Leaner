import Mathlib

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

theorem zpow_neg_one (A : M) : A ^ (-1 : ℤ) = A⁻¹ := by
  convert DivInvMonoid.zpow_neg' 0 A
  simp only [zpow_one, Int.ofNat_zero, Int.natCast_succ, zpow_eq_pow, zero_add]

