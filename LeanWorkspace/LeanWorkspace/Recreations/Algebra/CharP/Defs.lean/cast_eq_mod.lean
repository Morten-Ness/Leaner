import Mathlib

variable (R : Type*)

variable [AddMonoidWithOne R] (p : ℕ)

variable [CharP R p] {a b : ℕ}

theorem cast_eq_mod (k : ℕ) : (k : R) = (k % p : ℕ) := have (a : ℕ) : ((p * a : ℕ) : R) = 0 := by
    rw [CharP.cast_eq_zero_iff R p]
    exact Nat.dvd_mul_right p a
  calc
    (k : R) = ↑(k % p + p * (k / p)) := by rw [Nat.mod_add_div]
    _ = ↑(k % p) := by simp [this]

