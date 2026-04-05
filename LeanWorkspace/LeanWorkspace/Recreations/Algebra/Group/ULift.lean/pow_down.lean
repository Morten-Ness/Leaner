import Mathlib

variable {α : Type u} {β : Type v} {x y : ULift.{w} α}

theorem pow_down [Pow α β] (a : ULift.{w} α) (b : β) : (a ^ b).down = a.down ^ b := rfl

