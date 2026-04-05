import Mathlib

variable {R S : Type*}

variable [Ring R] {x y : R}

theorem Commute.sub_dvd_pow_sub_pow (h : Commute x y) (n : ℕ) : x - y ∣ x ^ n - y ^ n := Dvd.intro _ <| h.mul_geom_sum₂ _

