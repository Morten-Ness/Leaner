import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [hα : Archimedean α]
  {p : α} (hp : 0 < p)
  {a b c : α} {n : ℤ}

theorem toIcoMod_apply_left (a : α) : toIcoMod hp a a = a := by
  rw [toIcoMod_eq_iff hp, Set.left_mem_Ico]
  exact ⟨lt_add_of_pos_right _ hp, 0, by simp⟩

