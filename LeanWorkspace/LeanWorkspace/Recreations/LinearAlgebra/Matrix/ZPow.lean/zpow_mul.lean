import Mathlib

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

theorem zpow_mul (A : M) (h : IsUnit A.det) : ∀ m n : ℤ, A ^ (m * n) = (A ^ m) ^ n
  | (m : ℕ), (n : ℕ) => by
    rw [zpow_natCast, zpow_natCast, ← pow_mul, ← zpow_natCast, Int.natCast_mul]
  | (m : ℕ), -[n+1] => by
    rw [zpow_natCast, zpow_negSucc, ← pow_mul, ofNat_mul_negSucc, Matrix.zpow_neg_natCast]
  | -[m+1], (n : ℕ) => by
    rw [zpow_natCast, zpow_negSucc, ← Matrix.inv_pow', ← pow_mul, negSucc_mul_ofNat, Matrix.zpow_neg_natCast,
        Matrix.inv_pow']
  | -[m+1], -[n+1] => by
    rw [zpow_negSucc, zpow_negSucc, negSucc_mul_negSucc, ← Int.natCast_mul, zpow_natCast, Matrix.inv_pow',
      ← pow_mul, nonsing_inv_nonsing_inv]
    rw [det_pow]
    exact h.pow _
