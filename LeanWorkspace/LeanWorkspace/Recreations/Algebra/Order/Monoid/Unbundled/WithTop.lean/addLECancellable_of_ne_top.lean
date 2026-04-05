import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithTop α} {a b : α}

theorem addLECancellable_of_ne_top [LE α] [AddLeftReflectLE α]
    (hx : x ≠ ⊤) : AddLECancellable x := fun _b _c ↦ WithTop.le_of_add_le_add_left hx

