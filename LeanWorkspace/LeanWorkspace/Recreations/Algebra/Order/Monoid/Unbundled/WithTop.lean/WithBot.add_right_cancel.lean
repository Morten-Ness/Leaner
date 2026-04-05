import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithBot α} {a b : α}

theorem add_right_cancel [IsRightCancelAdd α] (hz : z ≠ ⊥) (h : x + z = y + z) : x = y := (WithBot.add_right_inj hz).1 h

