import Mathlib

variable {R S : Type*}

theorem pred_ne_self {α : Type*} [NonAssocRing α] [Nontrivial α] (a : α) : a - 1 ≠ a := fun h ↦
  one_ne_zero (neg_injective ((add_right_inj a).mp (by simp [← sub_eq_add_neg, h])))

