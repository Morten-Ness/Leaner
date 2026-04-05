import Mathlib

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

theorem zpow_add_of_nonneg {A : M} {m n : ℤ} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    A ^ (m + n) = A ^ m * A ^ n := by
  obtain ⟨k, rfl⟩ := eq_ofNat_of_zero_le hm
  obtain ⟨l, rfl⟩ := eq_ofNat_of_zero_le hn
  rw [← Int.natCast_add, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]

