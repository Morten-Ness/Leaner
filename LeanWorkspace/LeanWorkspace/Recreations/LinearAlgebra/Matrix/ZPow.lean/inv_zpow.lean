import Mathlib

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

theorem inv_zpow (A : M) : ∀ n : ℤ, A⁻¹ ^ n = (A ^ n)⁻¹
  | (n : ℕ) => by rw [zpow_natCast, zpow_natCast, Matrix.inv_pow']
  | -[n+1] => by rw [zpow_negSucc, zpow_negSucc, Matrix.inv_pow']
