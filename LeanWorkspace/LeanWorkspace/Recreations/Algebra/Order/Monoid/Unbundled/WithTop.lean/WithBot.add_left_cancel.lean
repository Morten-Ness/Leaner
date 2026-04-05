import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithBot α} {a b : α}

theorem add_left_cancel [IsLeftCancelAdd α] (hx : x ≠ ⊥) (h : x + y = x + z) : y = z := (WithBot.add_left_inj hx).1 h

