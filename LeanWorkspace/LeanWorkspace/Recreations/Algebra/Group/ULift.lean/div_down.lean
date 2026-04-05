import Mathlib

variable {α : Type u} {β : Type v} {x y : ULift.{w} α}

theorem div_down [Div α] : (x / y).down = x.down / y.down := rfl

