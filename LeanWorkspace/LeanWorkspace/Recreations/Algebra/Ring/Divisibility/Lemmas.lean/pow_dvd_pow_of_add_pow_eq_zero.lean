import Mathlib

variable {R : Type*}

variable {x y : R} {n m p : ℕ}

variable [Ring R]

theorem pow_dvd_pow_of_add_pow_eq_zero (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (h : (x + y) ^ n = 0) : x ^ m ∣ y ^ p := by
  rw [← neg_neg y, neg_pow']
  apply dvd_mul_of_dvd_left
  apply Commute.pow_dvd_pow_of_sub_pow_eq_zero h_comm.neg_right hp
  simpa

