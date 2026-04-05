import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoDiv_apply_left (a : α) : toIcoDiv hp a a = 0 := toIcoDiv_eq_of_sub_zsmul_mem_Ico hp <| by simp [hp]

