import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_mul_left [NormalizedGCDMonoid α] (a b c : α) :
    lcm (a * b) (a * c) = normalize a * lcm b c := (by_cases (by rintro rfl; simp))
    fun ha : a ≠ 0 =>
    suffices lcm (a * b) (a * c) = normalize (a * lcm b c) by simpa
    have : a ∣ lcm (a * b) (a * c) := (dvd_mul_right _ _).trans (dvd_lcm_left _ _)
    let ⟨_, eq⟩ := this
    lcm_eq_normalize
      (lcm_dvd (mul_dvd_mul_left a (dvd_lcm_left _ _)) (mul_dvd_mul_left a (dvd_lcm_right _ _)))
      (eq.symm ▸
        (mul_dvd_mul_left a <|
          lcm_dvd ((mul_dvd_mul_iff_left ha).1 <| eq ▸ dvd_lcm_left _ _)
            ((mul_dvd_mul_iff_left ha).1 <| eq ▸ dvd_lcm_right _ _)))

