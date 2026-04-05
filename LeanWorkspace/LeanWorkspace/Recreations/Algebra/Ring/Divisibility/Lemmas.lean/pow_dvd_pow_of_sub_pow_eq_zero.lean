import Mathlib

variable {R : Type*}

variable {x y : R} {n m p : ℕ}

variable [Ring R]

theorem pow_dvd_pow_of_sub_pow_eq_zero (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (h : (x - y) ^ n = 0) : x ^ m ∣ y ^ p := by
  rw [← sub_add_cancel y x]
  apply Commute.pow_dvd_add_pow_of_pow_eq_zero_left (h_comm.symm.sub_left rfl) hp _
  rw [← neg_sub x y, neg_pow, h, mul_zero]

