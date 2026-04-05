import Mathlib

variable {R ι : Type*}

variable [AddMonoidWithOne R]

theorem of_one_ne_zero_of_two_eq_zero (h₁ : (1 : R) ≠ 0) (h₂ : (2 : R) = 0) : CharP R 2 where
  cast_eq_zero_iff n := by
    obtain hn | hn := Nat.even_or_odd n
    · simp_rw [hn.two_dvd, iff_true]
      exact natCast_eq_zero_of_even_of_two_eq_zero hn h₂
    · simp_rw [hn.not_two_dvd_nat, iff_false]
      rwa [natCast_eq_one_of_odd_of_two_eq_zero hn h₂]

