import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem Ico_eq_locus_Ioc_eq_iUnion_Ioo :
    { b | toIcoMod hp a b = toIocMod hp a b } = ⋃ z : ℤ, Set.Ioo (a + z • p) (a + p + z • p) := by
  ext1
  simp_rw [Set.mem_setOf, Set.mem_iUnion, ← Set.sub_mem_Ioo_iff_left, ←
    AddCommGroup.not_modEq_iff_toIcoMod_eq_toIocMod, AddCommGroup.modEq_iff_forall_notMem_Ioo_mod hp, not_forall,
    Classical.not_not]

