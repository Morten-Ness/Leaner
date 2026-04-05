import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocDiv_sub_eq_toIocDiv_add (a b c : α) :
    toIocDiv hp a (b - c) = toIocDiv hp (a + c) b := by
  apply toIocDiv_eq_of_sub_zsmul_mem_Ioc
  rw [← sub_right_comm, Set.sub_mem_Ioc_iff_left, add_right_comm]
  exact sub_toIocDiv_zsmul_mem_Ioc hp (a + c) b

