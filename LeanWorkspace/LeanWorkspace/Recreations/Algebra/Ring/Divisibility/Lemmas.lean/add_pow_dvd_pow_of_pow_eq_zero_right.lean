import Mathlib

variable {R : Type*}

variable {x y : R} {n m p : ℕ}

variable [Ring R]

theorem add_pow_dvd_pow_of_pow_eq_zero_right (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hx : x ^ n = 0) : (x + y) ^ m ∣ y ^ p := Commute.pow_dvd_pow_of_sub_pow_eq_zero (h_comm.add_left rfl) hp (by simpa)

