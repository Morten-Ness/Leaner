import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithBot α} {a b : α}

theorem add_lt_add_of_le_of_lt [Preorder α] [AddLeftStrictMono α]
    [AddRightMono α] (hw : w ≠ ⊥) (hwy : w ≤ y) (hxz : x < z) :
    w + x < y + z := (WithBot.add_lt_add_left hw hxz).trans_le <| by gcongr

