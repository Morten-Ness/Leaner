import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem exists_associated_pow_of_mul_eq_pow [GCDMonoid α] {a b c : α} (hab : IsUnit (gcd a b))
    {k : ℕ} (h : a * b = c ^ k) : ∃ d : α, Associated (d ^ k) a := by
  cases subsingleton_or_nontrivial α
  · use 0
    rw [Subsingleton.elim a (0 ^ k)]
  by_cases ha : a = 0
  · use 0
    obtain rfl | hk := eq_or_ne k 0
    · simp [ha] at h
    · rw [ha, zero_pow hk]
  by_cases hb : b = 0
  · use 1
    rw [one_pow]
    apply (associated_one_iff_isUnit.mpr hab).symm.trans
    rw [hb]
    exact gcd_zero_right' a
  obtain rfl | hk := k.eq_zero_or_pos
  · use 1
    rw [pow_zero] at h ⊢
    use Units.mkOfMulEqOne _ _ h
    rw [Units.val_mkOfMulEqOne, one_mul]
  have hc : c ∣ a * b := by
    rw [h]
    exact dvd_pow_self _ hk.ne'
  obtain ⟨d₁, d₂, hd₁, hd₂, hc⟩ := exists_dvd_and_dvd_of_dvd_mul hc
  use d₁
  obtain ⟨h0₁, ⟨a', ha'⟩⟩ := pow_dvd_of_mul_eq_pow ha hab h hc hd₁
  rw [mul_comm] at h hc
  rw [(gcd_comm' a b).isUnit_iff] at hab
  obtain ⟨h0₂, ⟨b', hb'⟩⟩ := pow_dvd_of_mul_eq_pow hb hab h hc hd₂
  rw [ha', hb', hc, mul_pow] at h
  have h' : a' * b' = 1 := by
    apply (mul_right_inj' h0₁).mp
    rw [mul_one]
    apply (mul_right_inj' h0₂).mp
    rw [← h]
    rw [mul_assoc, mul_comm a', ← mul_assoc _ b', ← mul_assoc b', mul_comm b']
  use Units.mkOfMulEqOne _ _ h'
  rw [Units.val_mkOfMulEqOne, ha']

