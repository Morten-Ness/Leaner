import Mathlib

variable {α : Type u} {β : Type v} {x y : ULift.{w} α}

theorem one_down [One α] : (1 : ULift α).down = 1 := rfl

