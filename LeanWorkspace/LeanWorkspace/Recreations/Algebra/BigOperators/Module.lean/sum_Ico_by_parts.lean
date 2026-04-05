import Mathlib

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (f : ℕ → R) (g : ℕ → M) {m n : ℕ}

theorem sum_Ico_by_parts (hmn : m < n) :
    ∑ i ∈ Ico m n, f i • g i =
      f (n - 1) • G n - f m • G m - ∑ i ∈ Ico m (n - 1), (f (i + 1) - f i) • G (i + 1) := by
  have h₁ : (∑ i ∈ Ico (m + 1) n, f i • G i) = ∑ i ∈ Ico m (n - 1), f (i + 1) • G (i + 1) := by
    rw [← Nat.sub_add_cancel (Nat.one_le_of_lt hmn), ← sum_Ico_add']
    simp only [add_tsub_cancel_right]
  have h₂ :
    (∑ i ∈ Ico (m + 1) n, f i • G (i + 1)) =
      (∑ i ∈ Ico m (n - 1), f i • G (i + 1)) + f (n - 1) • G n - f m • G (m + 1) := by
    rw [← sum_Ico_sub_bot _ hmn, ← sum_Ico_succ_sub_top _ (Nat.le_sub_one_of_lt hmn),
      Nat.sub_add_cancel (pos_of_gt hmn), sub_add_cancel]
  rw [sum_eq_sum_Ico_succ_bot hmn]
  conv in (occs := 3) (f _ • g _) => rw [← sum_range_succ_sub_sum g]
  simp_rw [smul_sub, sum_sub_distrib, h₂, h₁]
  conv_lhs => congr; rfl; rw [← add_sub, add_comm, ← add_sub, ← sum_sub_distrib]
  have : ∀ i, f i • G (i + 1) - f (i + 1) • G (i + 1) = -((f (i + 1) - f i) • G (i + 1)) := by
    intro i
    rw [sub_smul]
    abel
  simp_rw [this, sum_neg_distrib, sum_range_succ, smul_add]
  abel

