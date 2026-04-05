import Mathlib

variable {R : Type*}

variable {x y : R} {n m p : ℕ}

variable [Ring R]

theorem pow_dvd_sub_pow_of_pow_eq_zero_right (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hy : y ^ n = 0) : x ^ m ∣ (x - y) ^ p := Commute.pow_dvd_pow_of_sub_pow_eq_zero (sub_right rfl h_comm) hp (by simpa)

