import Mathlib

variable {n' : Type*} [DecidableEq n'] [Fintype n'] {R : Type*} [CommRing R]

theorem zpow_add_one_of_ne_neg_one {A : M} : ∀ n : ℤ, n ≠ -1 → A ^ (n + 1) = A ^ n * A
  | (n : ℕ), _ => by simp only [pow_succ, ← Nat.cast_succ, zpow_natCast]
  | -1, h => absurd rfl h
  | -((n : ℕ) + 2), _ => by
    rcases nonsing_inv_cancel_or_zero A with (⟨h, _⟩ | h)
    · apply Matrix.zpow_add_one (isUnit_det_of_left_inverse h)
    · change A ^ (-((n + 1 : ℕ) : ℤ)) = A ^ (-((n + 2 : ℕ) : ℤ)) * A
      simp_rw [Matrix.zpow_neg_natCast, ← Matrix.inv_pow', h, zero_pow <| Nat.succ_ne_zero _, zero_mul]
