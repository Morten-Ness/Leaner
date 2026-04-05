import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_mem_Ico (a b : α) : toIcoMod hp a b ∈ Set.Ico a (a + p) := sub_toIcoDiv_zsmul_mem_Ico hp a b

