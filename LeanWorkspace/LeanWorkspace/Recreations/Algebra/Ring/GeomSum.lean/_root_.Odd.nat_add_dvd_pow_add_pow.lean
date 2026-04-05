import Mathlib

variable {R S : Type*}

variable {m k : ℕ} (x y n : ℕ)

theorem _root_.Odd.nat_add_dvd_pow_add_pow {n : ℕ} (h : Odd n) : x + y ∣ x ^ n + y ^ n := mod_cast Odd.add_dvd_pow_add_pow (x : ℤ) (↑y) h

