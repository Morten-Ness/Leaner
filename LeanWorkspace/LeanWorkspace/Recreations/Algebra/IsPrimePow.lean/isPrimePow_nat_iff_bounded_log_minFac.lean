import Mathlib

variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

theorem isPrimePow_nat_iff_bounded_log_minFac (n : ℕ) :
    IsPrimePow n
      ↔ ∃ k : ℕ, k ≤ Nat.log 2 n ∧ 0 < k ∧ n = n.minFac ^ k := by
  rw [isPrimePow_nat_iff_bounded_log]
  obtain rfl | h := eq_or_ne n 1
  · simp
  constructor
  · rintro ⟨k, hkle, hk_pos, p, hle, heq, hprime⟩
    refine ⟨k, hkle, hk_pos, ?_⟩
    rw [heq, hprime.pow_minFac hk_pos.ne']
  · rintro ⟨k, hkle, hk_pos, heq⟩
    refine ⟨k, hkle, hk_pos, n.minFac, Nat.minFac_le ?_, heq, ?_⟩
    · grind [Nat.minFac_prime_iff, nonpos_iff_eq_zero, Nat.log_zero_right, lt_self_iff_false]
    · grind [Nat.minFac_prime_iff]

