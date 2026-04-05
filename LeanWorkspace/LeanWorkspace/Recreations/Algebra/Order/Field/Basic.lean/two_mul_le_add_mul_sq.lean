import Mathlib

variable {ι α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b c d : α} {n : ℤ}

private theorem exists_lt_mul_left_of_nonneg {a b c : α} (ha : 0 ≤ a) (hc : 0 ≤ c) (h : c < a * b) :
    ∃ a' ∈ Set.Ico 0 a, c < a' * b := by
  have hb : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
  obtain ⟨a', ha', a_a'⟩ := exists_between ((div_lt_iff₀ hb).2 h)
  exact ⟨a', ⟨(div_nonneg hc hb.le).trans ha'.le, a_a'⟩, (div_lt_iff₀ hb).1 ha'⟩


private theorem exists_lt_mul_right_of_nonneg {a b c : α} (ha : 0 ≤ a) (hc : 0 ≤ c) (h : c < a * b) :
    ∃ b' ∈ Set.Ico 0 b, c < a * b' := by
  have hb : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
  simp_rw [mul_comm a] at h ⊢
  exact exists_lt_mul_left_of_nonneg hb.le hc h


private theorem exists_mul_left_lt₀ {a b c : α} (hc : a * b < c) : ∃ a' > a, a' * b < c := by
  rcases le_or_gt b 0 with hb | hb
  · obtain ⟨a', ha'⟩ := exists_gt a
    exact ⟨a', ha', hc.trans_le' (antitone_mul_right hb ha'.le)⟩
  · obtain ⟨a', ha', hc'⟩ := exists_between ((lt_div_iff₀ hb).2 hc)
    exact ⟨a', ha', (lt_div_iff₀ hb).1 hc'⟩


private theorem exists_mul_right_lt₀ {a b c : α} (hc : a * b < c) : ∃ b' > b, a * b' < c := by
  simp_rw [mul_comm a] at hc ⊢; exact exists_mul_left_lt₀ hc


theorem two_mul_le_add_mul_sq {ε : α} (hε : 0 < ε) :
    2 * a * b ≤ ε * a ^ 2 + ε⁻¹ * b ^ 2 := by
  have h : 2 * (ε * a) * b ≤ (ε * a) ^ 2 + b ^ 2 := two_mul_le_add_sq (ε * a) b
  calc 2 * a * b
  _ = 2 * a * b * (ε * ε⁻¹) := by rw [mul_inv_cancel₀ hε.ne', mul_one]
  _ = (2 * (ε * a) * b) * ε⁻¹ := by simp_rw [mul_assoc, mul_comm ε, mul_assoc]
  _ ≤ ((ε * a) ^ 2 + b ^ 2) * ε⁻¹ := by gcongr; exact inv_nonneg.mpr hε.le
  _ = ε * a ^ 2 + ε⁻¹ * b ^ 2 := by
    rw [mul_comm _ ε⁻¹, mul_pow, mul_add, ← mul_assoc, pow_two, ← mul_assoc, inv_mul_cancel₀ hε.ne',
      one_mul]

