import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_mul_left' [GCDMonoid α] (a b c : α) :
    Associated (gcd (a * b) (a * c)) (a * gcd b c) := by
  obtain rfl | ha := eq_or_ne a 0
  · simp only [zero_mul, gcd_zero_left']
  obtain ⟨d, eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c)
  apply associated_of_dvd_dvd
  · rw [eq]
    gcongr
    exact
      dvd_gcd ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_left _ _)
        ((mul_dvd_mul_iff_left ha).1 <| eq ▸ gcd_dvd_right _ _)
  · exact dvd_gcd (mul_dvd_mul_left a <| gcd_dvd_left _ _) (mul_dvd_mul_left a <| gcd_dvd_right _ _)

