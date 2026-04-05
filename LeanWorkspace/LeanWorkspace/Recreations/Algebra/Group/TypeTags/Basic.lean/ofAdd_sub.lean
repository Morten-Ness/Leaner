import Mathlib

variable {α : Type u} {β : Type v}

theorem ofAdd_sub [Sub α] (x y : α) : Multiplicative.ofAdd (x - y) = Multiplicative.ofAdd x / Multiplicative.ofAdd y := rfl

