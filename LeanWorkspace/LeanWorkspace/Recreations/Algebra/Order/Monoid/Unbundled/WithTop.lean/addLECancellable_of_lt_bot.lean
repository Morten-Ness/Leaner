import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithBot α} {a b : α}

theorem addLECancellable_of_lt_bot [Preorder α] [AddLeftReflectLE α]
    (hx : x < ⊥) : AddLECancellable x := WithBot.addLECancellable_of_ne_bot hx.ne

