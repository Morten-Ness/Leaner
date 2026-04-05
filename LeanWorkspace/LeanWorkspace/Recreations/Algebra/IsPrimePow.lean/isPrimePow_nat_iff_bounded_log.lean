import Mathlib

variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

theorem isPrimePow_nat_iff_bounded_log (n : ℕ) :
    IsPrimePow n
      ↔ ∃ k : ℕ, k ≤ Nat.log 2 n ∧ 0 < k ∧ ∃ p : ℕ, p ≤ n ∧ n = p ^ k ∧ p.Prime := by
  rw [isPrimePow_nat_iff]
  constructor
  · rintro ⟨p, k, hp', hk', rfl⟩
    refine ⟨k, ?_, hk', ⟨p, Nat.le_pow hk', rfl, hp'⟩⟩
    · calc
        k = Nat.log 2 (2 ^ k) := by simp
        _ ≤ Nat.log 2 (p ^ k) := Nat.log_mono Nat.one_lt_two Nat.AtLeastTwo.prop
                                   (Nat.pow_le_pow_left (Nat.Prime.two_le hp') k)
  · rintro ⟨k, hk, hk', ⟨p, hp, rfl, hp'⟩⟩
    exact ⟨p, k, hp', hk', rfl⟩

