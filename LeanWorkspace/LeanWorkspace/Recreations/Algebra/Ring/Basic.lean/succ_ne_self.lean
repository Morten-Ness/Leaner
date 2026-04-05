import Mathlib

variable {R S : Type*}

theorem succ_ne_self {α : Type*} [NonAssocRing α] [Nontrivial α] (a : α) : a + 1 ≠ a := fun h =>
  one_ne_zero ((add_right_inj a).mp (by simp [h]))

