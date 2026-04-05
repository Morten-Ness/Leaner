import Mathlib

variable {S : Type*} [UnitalShelf S]

theorem act_idem (x : S) : (x ◃ x) = x := by rw [← act_one x, ← Shelf.self_distrib, act_one]

