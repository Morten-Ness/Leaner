import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIocMod_apply_left (a : α) : toIocMod hp a a = a + p := by
  rw [toIocMod_eq_iff hp, Set.right_mem_Ioc]
  exact ⟨lt_add_of_pos_right _ hp, -1, by simp⟩

