import Mathlib

variable {α : Type u} {β : Type v} {x y : ULift.{w} α}

theorem inv_down [Inv α] : x⁻¹.down = x.down⁻¹ := rfl

