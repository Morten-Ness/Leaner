import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocDiv_add_zsmul (a b : α) (m : ℤ) : toIocDiv hp a (b + m • p) = toIocDiv hp a b + m := toIocDiv_eq_of_sub_zsmul_mem_Ioc hp <| by
    simpa only [add_smul, add_sub_add_right_eq_sub] using sub_toIocDiv_zsmul_mem_Ioc hp a b

