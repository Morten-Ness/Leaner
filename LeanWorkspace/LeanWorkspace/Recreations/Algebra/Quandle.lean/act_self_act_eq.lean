import Mathlib

variable {S : Type*} [UnitalShelf S]

theorem act_self_act_eq (x y : S) : x ◃ (x ◃ y) = x ◃ y := by
  have h : x ◃ (x ◃ y) = (x ◃ 1) ◃ (x ◃ y) := by rw [act_one]
  rw [h, ← Shelf.self_distrib, one_act]

