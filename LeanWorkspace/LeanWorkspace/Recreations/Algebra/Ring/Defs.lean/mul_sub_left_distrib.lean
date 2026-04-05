import Mathlib

variable {α : Type u} {R : Type v}

variable [NonUnitalNonAssocRing α]

theorem mul_sub_left_distrib (a b c : α) : a * (b - c) = a * b - a * c := by
  simpa only [sub_eq_add_neg, neg_mul_eq_mul_neg] using mul_add a b (-c)

alias mul_sub := mul_sub_left_distrib

