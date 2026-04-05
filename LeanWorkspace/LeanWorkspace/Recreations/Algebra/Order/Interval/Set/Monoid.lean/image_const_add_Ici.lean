import Mathlib

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedCancelAddMonoid M]
  [ExistsAddOfLE M] (a b c d : M)

theorem image_const_add_Ici : (fun x => a + x) '' Ici b = Ici (a + b) := by
  simp only [add_comm a, Set.image_add_const_Ici]

