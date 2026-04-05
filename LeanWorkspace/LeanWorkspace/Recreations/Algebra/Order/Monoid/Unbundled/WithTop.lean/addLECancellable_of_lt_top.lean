import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithTop α} {a b : α}

theorem addLECancellable_of_lt_top [Preorder α] [AddLeftReflectLE α]
    (hx : x < ⊤) : AddLECancellable x := WithTop.addLECancellable_of_ne_top hx.ne

