import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

theorem gcd_eq_zero_iff {a b : R} : gcd a b = 0 ↔ a = 0 ∧ b = 0 := ⟨fun h => by simpa [h] using EuclideanDomain.gcd_dvd a b, by
    rintro ⟨rfl, rfl⟩
    exact EuclideanDomain.gcd_zero_right _⟩

