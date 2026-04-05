import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

theorem abs_max_sub_max_le_max (a b c d : α) : |max a b - max c d| ≤ max |a - c| |b - d| := by
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · exact (max_sub_max_le_max _ _ _ _).trans (max_le_max (le_abs_self _) (le_abs_self _))
  · rw [abs_sub_comm a c, abs_sub_comm b d]
    exact (max_sub_max_le_max _ _ _ _).trans (max_le_max (le_abs_self _) (le_abs_self _))

