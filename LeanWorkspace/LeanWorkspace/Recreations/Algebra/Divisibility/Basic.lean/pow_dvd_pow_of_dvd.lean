import Mathlib

variable {α : Type*}

variable [CommMonoid α] {a b : α}

theorem pow_dvd_pow_of_dvd (h : a ∣ b) (n : ℕ) : a ^ n ∣ b ^ n := by
  induction n with
  | zero => simp
  | succ =>
    rw [pow_succ, pow_succ]
    gcongr

