import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem tfae_modEq :
    TFAE
      [a ≡ b [PMOD p], ∀ z : ℤ, b - z • p ∉ Set.Ioo a (a + p), toIcoMod hp a b ≠ toIocMod hp a b,
        toIcoMod hp a b + p = toIocMod hp a b] := by
  rw [AddCommGroup.modEq_iff_toIcoMod_eq_left hp]
  tfae_have 3 → 2 := by
    rw [← not_exists, not_imp_not]
    exact fun ⟨i, hi⟩ =>
      ((toIcoMod_eq_iff hp).2 ⟨Set.Ioo_subset_Ico_self hi, i, (sub_add_cancel b _).symm⟩).trans
        ((toIocMod_eq_iff hp).2 ⟨Set.Ioo_subset_Ioc_self hi, i, (sub_add_cancel b _).symm⟩).symm
  tfae_have 4 → 3
  | h => by
    rw [← h, Ne, eq_comm, add_eq_left]
    exact hp.ne'
  tfae_have 1 → 4
  | h => by
    rw [h, eq_comm, toIocMod_eq_iff, Set.right_mem_Ioc]
    refine ⟨lt_add_of_pos_right a hp, toIcoDiv hp a b - 1, ?_⟩
    rw [sub_one_zsmul, add_add_add_comm, add_neg_cancel, add_zero]
    conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul hp a b, h]
  tfae_have 2 → 1 := by
    rw [← not_exists, not_imp_comm]
    have h' := toIcoMod_mem_Ico hp a b
    exact fun h => ⟨_, h'.1.lt_of_ne' h, h'.2⟩
  tfae_finish

