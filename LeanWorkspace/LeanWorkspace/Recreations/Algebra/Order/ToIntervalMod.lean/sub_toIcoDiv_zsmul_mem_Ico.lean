import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem sub_toIcoDiv_zsmul_mem_Ico (a b : α) : b - toIcoDiv hp a b • p ∈ Set.Ico a (a + p) := (existsUnique_sub_zsmul_mem_Ico hp b a).choose_spec.1

