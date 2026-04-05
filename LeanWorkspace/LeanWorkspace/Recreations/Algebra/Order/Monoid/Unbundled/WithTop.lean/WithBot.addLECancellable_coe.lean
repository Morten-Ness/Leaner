import Mathlib

variable {α : Type u} {β : Type v}

variable [Add α] {w x y z : WithBot α} {a b : α}

theorem addLECancellable_coe [LE α] [AddLeftReflectLE α] (a : α) :
    AddLECancellable (a : WithBot α) := WithBot.addLECancellable_of_ne_bot coe_ne_bot

