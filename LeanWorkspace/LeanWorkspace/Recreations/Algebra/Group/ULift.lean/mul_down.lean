import Mathlib

variable {α : Type u} {β : Type v} {x y : ULift.{w} α}

theorem mul_down [Mul α] : (x * y).down = x.down * y.down := rfl

