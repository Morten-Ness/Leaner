import Mathlib

variable {α : Type u} {R : Type v}

variable [NonUnitalNonAssocRing α]

theorem mul_sub_right_distrib (a b c : α) : (a - b) * c = a * c - b * c := by
  simpa only [sub_eq_add_neg, neg_mul_eq_neg_mul] using add_mul a (-b) c

alias sub_mul := mul_sub_right_distrib

