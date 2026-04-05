import Mathlib

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

theorem transpose_zpow (A : M) : ∀ n : ℤ, (A ^ n)ᵀ = Aᵀ ^ n
  | (n : ℕ) => by rw [zpow_natCast, zpow_natCast, transpose_pow]
  | -[n+1] => by rw [zpow_negSucc, zpow_negSucc, transpose_nonsing_inv, transpose_pow]
