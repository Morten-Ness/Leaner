import Mathlib

variable {S : Type*} [UnitalShelf S]

theorem assoc (x y z : S) : (x ◃ y) ◃ z = x ◃ y ◃ z := by
  rw [self_distrib, self_distrib, UnitalShelf.act_act_self_eq, UnitalShelf.act_self_act_eq]

