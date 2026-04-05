import Mathlib

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

theorem zero_zpow : ∀ z : ℤ, z ≠ 0 → (0 : M) ^ z = 0
  | (n : ℕ), h => by
    rw [zpow_natCast, zero_pow]
    exact mod_cast h
  | -[n+1], _ => by simp [zero_pow n.succ_ne_zero]
