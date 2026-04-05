import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoDiv_sub_eq_toIcoDiv_add (a b c : α) :
    toIcoDiv hp a (b - c) = toIcoDiv hp (a + c) b := by
  apply toIcoDiv_eq_of_sub_zsmul_mem_Ico
  rw [← sub_right_comm, Set.sub_mem_Ico_iff_left, add_right_comm]
  exact sub_toIcoDiv_zsmul_mem_Ico hp (a + c) b

