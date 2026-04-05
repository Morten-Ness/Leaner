import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Int.fract_periodic (α) [Ring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α] :
    Function.Periodic Int.fract (1 : α) := fun a => mod_cast Int.fract_add_intCast a 1

