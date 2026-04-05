import Mathlib

variable {ι α β M N G k R : Type*}

theorem card_le_card_toFinset_add_one_iff [DecidableEq α] {m : Multiset α} :
    m.card ≤ m.toFinset.card + 1 ↔
      ∀ x y, 1 < m.count x → 1 < m.count y → x = y ∧ m.count x = 2 := by
  rw [← m.toFinset_sum_count_eq, m.toFinset.card_eq_sum_ones, ← tsub_le_iff_left,
    ← Finset.sum_tsub_distrib _ (by simp [one_le_count_iff_mem]), Finset.sum_le_one_iff]
  simp only [← pos_iff_ne_zero, Nat.sub_pos_iff_lt, mem_toFinset, Nat.pred_eq_succ_iff]
  exact ⟨fun h x y hx hy ↦ h x y (one_le_count_iff_mem.mp hx.le)
    (one_le_count_iff_mem.mp hy.le) hx hy, fun h x y _ _ hx hy ↦ h x y hx hy⟩

