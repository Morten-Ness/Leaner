import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoDiv_neg (a b : α) : toIcoDiv hp a (-b) = -(toIocDiv hp (-a) b + 1) := by
  suffices toIcoDiv hp a (-b) = -toIocDiv hp (-(a + p)) b by
    rwa [neg_add, ← sub_eq_add_neg, toIocDiv_sub_eq_toIocDiv_add', toIocDiv_add_right] at this
  rw [← neg_eq_iff_eq_neg, eq_comm]
  apply toIocDiv_eq_of_sub_zsmul_mem_Ioc
  obtain ⟨hc, ho⟩ := sub_toIcoDiv_zsmul_mem_Ico hp a (-b)
  rw [← neg_lt_neg_iff, neg_sub' (-b), neg_neg, ← neg_smul] at ho
  rw [← neg_le_neg_iff, neg_sub' (-b), neg_neg, ← neg_smul] at hc
  refine ⟨ho, hc.trans_eq ?_⟩
  rw [neg_add, neg_add_cancel_right]

