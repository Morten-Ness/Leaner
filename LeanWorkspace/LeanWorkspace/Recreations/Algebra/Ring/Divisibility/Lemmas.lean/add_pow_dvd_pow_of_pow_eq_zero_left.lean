import Mathlib

variable {R : Type*}

variable {x y : R} {n m p : ℕ}

variable [Ring R]

theorem add_pow_dvd_pow_of_pow_eq_zero_left (hp : n + m ≤ p + 1) (h_comm : Commute x y)
    (hy : y ^ n = 0) : (x + y) ^ m ∣ x ^ p := add_comm x y ▸ Commute.add_pow_dvd_pow_of_pow_eq_zero_right h_comm.symm hp hy

