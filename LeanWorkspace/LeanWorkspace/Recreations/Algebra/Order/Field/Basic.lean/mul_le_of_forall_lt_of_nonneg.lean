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


theorem mul_le_of_forall_lt_of_nonneg {a b c : α} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ a' ≥ 0, a' < a → ∀ b' ≥ 0, b' < b → a' * b' ≤ c) : a * b ≤ c := by
  refine le_of_forall_lt_imp_le_of_dense fun d d_ab ↦ ?_
  rcases lt_or_ge d 0 with hd | hd
  · exact hd.le.trans hc
  obtain ⟨a', ha', d_ab⟩ := exists_lt_mul_left_of_nonneg ha hd d_ab
  obtain ⟨b', hb', d_ab⟩ := exists_lt_mul_right_of_nonneg ha'.1 hd d_ab
  exact d_ab.le.trans (h a' ha'.1 ha'.2 b' hb'.1 hb'.2)

  -- surely there is an easier proof of this, or we already have something like it somewhere.
  -- It doesn't even need `α` to be a field, so it doesn't belong in this file.

