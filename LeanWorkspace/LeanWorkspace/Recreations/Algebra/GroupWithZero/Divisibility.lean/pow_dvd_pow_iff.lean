import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [IsCancelMulZero α] {a b : α} {m n : ℕ}

theorem pow_dvd_pow_iff (ha₀ : a ≠ 0) (ha : ¬IsUnit a) : a ^ n ∣ a ^ m ↔ n ≤ m := by
  constructor
  · intro h
    rw [← not_lt]
    intro hmn
    apply ha
    have : a ^ m * a ∣ a ^ m * 1 := by
      rw [← pow_succ, mul_one]
      exact (pow_dvd_pow _ (Nat.succ_le_of_lt hmn)).trans h
    rwa [mul_dvd_mul_iff_left, ← isUnit_iff_dvd_one] at this
    apply pow_ne_zero m ha₀
  · apply pow_dvd_pow

