import Mathlib

variable {M N : Type*}

variable [CommMonoidWithZero M] [IsCancelMulZero M]

theorem Prime.pow_dvd_of_dvd_mul_left {p a b : M} (hp : Prime p)
    (n : ℕ) (h : ¬p ∣ a) (h' : p ^ n ∣ a * b) : p ^ n ∣ b := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact one_dvd b
  | succ n ih =>
    obtain ⟨c, rfl⟩ := ih (dvd_trans (pow_dvd_pow p n.le_succ) h')
    rw [pow_succ]
    apply mul_dvd_mul_left _ ((hp.dvd_or_dvd _).resolve_left h)
    rwa [← mul_dvd_mul_iff_left (pow_ne_zero n hp.ne_zero), ← pow_succ, mul_left_comm]

