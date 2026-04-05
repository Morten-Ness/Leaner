import Mathlib

variable {α β : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  {abv : β → α} [IsAbsoluteValue abv]
  {f g : ℕ → β} {a : ℕ → α}

variable [Archimedean α]

theorem series_ratio_test {f : ℕ → β} (n : ℕ) (r : α) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ m, n ≤ m → abv (f m.succ) ≤ r * abv (f m)) :
    IsCauSeq abv fun m ↦ ∑ n ∈ range m, f n := by
  have har1 : |r| < 1 := by rwa [abs_of_nonneg hr0]
  refine (IsCauSeq.geo_series_const (abv (f n.succ) * r⁻¹ ^ n.succ) har1).of_abv_le n.succ fun m hmn ↦ ?_
  obtain rfl | hr := hr0.eq_or_lt
  · have m_pos := lt_of_lt_of_le (Nat.succ_pos n) hmn
    have := h m.pred (Nat.le_of_succ_le_succ (by rwa [Nat.succ_pred_eq_of_pos m_pos]))
    simpa [Nat.sub_add_cancel m_pos, pow_succ] using this
  generalize hk : m - n.succ = k
  replace hk : m = k + n.succ := (tsub_eq_iff_eq_add_of_le hmn).1 hk
  induction k generalizing m n with
  | zero =>
    rw [hk, Nat.zero_add, mul_right_comm, inv_pow _ _, ← div_eq_mul_inv, mul_div_cancel_right₀]
    positivity
  | succ k ih =>
    have kn : k + n.succ ≥ n.succ := by
      rw [← zero_add n.succ]; exact add_le_add (Nat.zero_le _) (by simp)
    rw [hk, Nat.succ_add, pow_succ r, ← mul_assoc]
    refine
      le_trans (by rw [mul_comm] <;> exact h _ (Nat.le_of_succ_le kn))
        (mul_le_mul_of_nonneg_right ?_ hr0)
    exact ih _ h _ (by simp) rfl

