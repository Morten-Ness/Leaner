import Mathlib

variable {M : Type*}

variable [CommMonoidWithZero M]

variable {p : M} (hp : Prime p)

theorem dvd_of_dvd_pow {a : M} {n : ℕ} (h : p ∣ a ^ n) : p ∣ a := by
  induction n with
  | zero =>
    rw [pow_zero] at h
    have := isUnit_of_dvd_one h
    have := Prime.not_unit hp
    contradiction
  | succ n ih =>
    rw [pow_succ'] at h
    rcases Prime.dvd_or_dvd hp h with dvd_a | dvd_pow
    · assumption
    · exact ih dvd_pow

