import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_pow_right_dvd_pow_gcd [GCDMonoid α] {a b : α} {k : ℕ} :
    gcd a (b ^ k) ∣ gcd a b ^ k := by
  by_cases hg : gcd a b = 0
  · rw [gcd_eq_zero_iff] at hg
    rcases hg with ⟨rfl, rfl⟩
    exact
      (gcd_zero_left' (0 ^ k : α)).dvd.trans
        (pow_dvd_pow_of_dvd (gcd_zero_left' (0 : α)).symm.dvd _)
  · induction k with
    | zero => rw [pow_zero, pow_zero]; exact (gcd_one_right' a).dvd
    | succ k hk =>
      rw [pow_succ', pow_succ']
      trans gcd a b * gcd a (b ^ k)
      · exact gcd_mul_dvd_mul_gcd a b (b ^ k)
      · exact (mul_dvd_mul_iff_left hg).mpr hk

