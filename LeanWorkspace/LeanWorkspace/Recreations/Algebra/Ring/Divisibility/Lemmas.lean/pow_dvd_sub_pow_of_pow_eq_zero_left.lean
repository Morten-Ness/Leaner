import Mathlib

variable {R : Type*}

variable {x y : R} {n m p : ℕ}

variable [Ring R]

theorem pow_dvd_sub_pow_of_pow_eq_zero_left (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hx : x ^ n = 0) : y ^ m ∣ (x - y) ^ p := by
  rw [← neg_sub y x, neg_pow']
  apply dvd_mul_of_dvd_left
  exact Commute.pow_dvd_sub_pow_of_pow_eq_zero_right h_comm.symm hp hx

