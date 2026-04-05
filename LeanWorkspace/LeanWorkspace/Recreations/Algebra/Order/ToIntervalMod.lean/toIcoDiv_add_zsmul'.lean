import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoDiv_add_zsmul' (a b : α) (m : ℤ) :
    toIcoDiv hp (a + m • p) b = toIcoDiv hp a b - m := by
  refine toIcoDiv_eq_of_sub_zsmul_mem_Ico _ ?_
  rw [sub_smul, ← sub_add, add_right_comm]
  simpa using sub_toIcoDiv_zsmul_mem_Ico hp a b

