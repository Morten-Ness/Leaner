import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoDiv_add_zsmul (a b : α) (m : ℤ) : toIcoDiv hp a (b + m • p) = toIcoDiv hp a b + m := toIcoDiv_eq_of_sub_zsmul_mem_Ico hp <| by
    simpa only [add_smul, add_sub_add_right_eq_sub] using sub_toIcoDiv_zsmul_mem_Ico hp a b

