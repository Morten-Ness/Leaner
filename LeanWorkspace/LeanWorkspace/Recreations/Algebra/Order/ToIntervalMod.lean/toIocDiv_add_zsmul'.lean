import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocDiv_add_zsmul' (a b : α) (m : ℤ) :
    toIocDiv hp (a + m • p) b = toIocDiv hp a b - m := by
  refine toIocDiv_eq_of_sub_zsmul_mem_Ioc _ ?_
  rw [sub_smul, ← sub_add, add_right_comm]
  simpa using sub_toIocDiv_zsmul_mem_Ioc hp a b

