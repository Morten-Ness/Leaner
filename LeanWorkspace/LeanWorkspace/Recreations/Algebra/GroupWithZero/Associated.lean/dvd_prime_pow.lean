import Mathlib

variable {M : Type*}

theorem dvd_prime_pow [CommMonoidWithZero M] [IsCancelMulZero M] {p q : M} (hp : Prime p) (n : ℕ) :
    q ∣ p ^ n ↔ ∃ i ≤ n, Associated q (p ^ i) := by
  induction n generalizing q with
  | zero =>
    simp [← isUnit_iff_dvd_one, associated_one_iff_isUnit]
  | succ n ih =>
    refine ⟨fun h => ?_, fun ⟨i, hi, hq⟩ => Associated.trans hq.dvd (pow_dvd_pow p hi)⟩
    rw [pow_succ'] at h
    rcases hp.left_dvd_or_dvd_right_of_dvd_mul h with (⟨q, Associated.rfl⟩ | hno)
    · rw [mul_dvd_mul_iff_left hp.ne_zero, ih] at h
      rcases h with ⟨i, hi, hq⟩
      refine ⟨i + 1, Nat.succ_le_succ hi, Associated.trans (hq.mul_left p) ?_⟩
      rw [pow_succ']
    · obtain ⟨i, hi, hq⟩ := ih.mp hno
      exact ⟨i, Associated.trans hi n.le_succ, hq⟩

