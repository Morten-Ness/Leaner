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


theorem uniform_continuous_npow_on_bounded (B : α) {ε : α} (hε : 0 < ε) (n : ℕ) :
    ∃ δ > 0, ∀ q r : α, |r| ≤ B → |q - r| ≤ δ → |q ^ n - r ^ n| < ε := by
  wlog! B_pos : 0 < B generalizing B
  · have ⟨δ, δ_pos, cont⟩ := this 1 zero_lt_one
    exact ⟨δ, δ_pos, fun q r hr ↦ cont q r (hr.trans (B_pos.trans zero_le_one))⟩
  have pos : 0 < 1 + ↑n * (B + 1) ^ (n - 1) := zero_lt_one.trans_le <| le_add_of_nonneg_right <|
    mul_nonneg n.cast_nonneg <| (pow_pos (B_pos.trans <| lt_add_of_pos_right _ zero_lt_one) _).le
  refine ⟨min 1 (ε / (1 + n * (B + 1) ^ (n - 1))), lt_min zero_lt_one (div_pos hε pos),
    fun q r hr hqr ↦ (abs_pow_sub_pow_le ..).trans_lt ?_⟩
  rw [le_inf_iff, le_div_iff₀ pos, mul_one_add, ← mul_assoc] at hqr
  obtain h | h := (abs_nonneg (q - r)).eq_or_lt
  · simpa only [← h, zero_mul] using hε
  refine (lt_of_le_of_lt ?_ <| lt_add_of_pos_left _ h).trans_le hqr.2
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ((abs_nonneg _).trans le_sup_left) ?_ _)
    (mul_nonneg (abs_nonneg _) n.cast_nonneg)
  refine max_le ?_ (hr.trans <| le_add_of_nonneg_right zero_le_one)
  exact add_sub_cancel r q ▸ (abs_add_le ..).trans (add_le_add hr hqr.1)

