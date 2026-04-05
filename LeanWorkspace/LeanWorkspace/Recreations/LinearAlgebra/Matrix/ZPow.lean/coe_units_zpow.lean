import Mathlib

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

theorem coe_units_zpow (u : Mˣ) : ∀ n : ℤ, ((u ^ n : Mˣ) : M) = (u : M) ^ n
  | (n : ℕ) => by rw [zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
  | -[k+1] => by
    rw [zpow_negSucc, zpow_negSucc, ← inv_pow, u⁻¹.val_pow_eq_pow_val, ← Matrix.inv_pow', coe_units_inv]
