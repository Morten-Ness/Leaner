import Mathlib

variable {S : Type*} [UnitalShelf S]

theorem act_act_self_eq (x y : S) : (x ◃ y) ◃ x = x ◃ y := by
  have h : (x ◃ y) ◃ x = (x ◃ y) ◃ (x ◃ 1) := by rw [act_one]
  rw [h, ← Shelf.self_distrib, act_one]

