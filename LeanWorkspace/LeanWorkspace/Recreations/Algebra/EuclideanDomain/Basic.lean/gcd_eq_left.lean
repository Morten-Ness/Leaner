import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

theorem gcd_eq_left {a b : R} : gcd a b = a ↔ a ∣ b := ⟨fun h => by
    rw [← h]
    apply EuclideanDomain.gcd_dvd_right, fun h => by rw [EuclideanDomain.gcd_val, EuclideanDomain.mod_eq_zero.2 h, gcd_zero_left]⟩

