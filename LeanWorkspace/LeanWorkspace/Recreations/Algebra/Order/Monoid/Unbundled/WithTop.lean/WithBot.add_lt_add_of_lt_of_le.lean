import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithBot α} {a b : α}

theorem add_lt_add_of_lt_of_le [Preorder α] [AddLeftMono α]
    [AddRightStrictMono α] (hx : x ≠ ⊥) (hwy : w < y) (hxz : x ≤ z) :
    w + x < y + z := (WithBot.add_lt_add_right hx hwy).trans_le <| by gcongr

