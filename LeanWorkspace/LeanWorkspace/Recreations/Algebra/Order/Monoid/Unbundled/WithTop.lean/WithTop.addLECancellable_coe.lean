import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithTop α} {a b : α}

theorem addLECancellable_coe [LE α] [AddLeftReflectLE α] (a : α) :
    AddLECancellable (a : WithTop α) := WithTop.addLECancellable_of_ne_top coe_ne_top

