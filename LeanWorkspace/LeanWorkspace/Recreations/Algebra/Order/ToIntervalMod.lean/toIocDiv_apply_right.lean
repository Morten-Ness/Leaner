import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocDiv_apply_right (a : α) : toIocDiv hp a (a + p) = 0 := toIocDiv_eq_of_sub_zsmul_mem_Ioc hp <| by simp [hp]

