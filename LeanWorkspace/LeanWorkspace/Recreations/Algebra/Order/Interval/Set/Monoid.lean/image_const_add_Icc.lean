import Mathlib

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedCancelAddMonoid M]
  [ExistsAddOfLE M] (a b c d : M)

theorem image_const_add_Icc : (fun x => a + x) '' Icc b c = Icc (a + b) (a + c) := by
  simp only [add_comm a, Set.image_add_const_Icc]

