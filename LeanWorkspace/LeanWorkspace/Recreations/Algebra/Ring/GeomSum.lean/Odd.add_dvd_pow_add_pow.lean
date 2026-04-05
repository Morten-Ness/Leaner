import Mathlib

variable {R S : Type*}

variable [CommRing R]

theorem Odd.add_dvd_pow_add_pow (x y : R) {n : ℕ} (h : Odd n) : x + y ∣ x ^ n + y ^ n := by
  have h₁ := geom_sum₂_mul x (-y) n
  rw [Odd.neg_pow h y, sub_neg_eq_add, sub_neg_eq_add] at h₁
  exact Dvd.intro_left _ h₁

