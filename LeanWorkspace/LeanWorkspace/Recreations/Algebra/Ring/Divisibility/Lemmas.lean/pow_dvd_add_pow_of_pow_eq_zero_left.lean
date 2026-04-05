import Mathlib

variable {R : Type*}

variable {x y : R} {n m p : ℕ}

variable [Semiring R]

theorem pow_dvd_add_pow_of_pow_eq_zero_left (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hx : x ^ n = 0) : y ^ m ∣ (x + y) ^ p := add_comm x y ▸ Commute.pow_dvd_add_pow_of_pow_eq_zero_right h_comm.symm hp hx

