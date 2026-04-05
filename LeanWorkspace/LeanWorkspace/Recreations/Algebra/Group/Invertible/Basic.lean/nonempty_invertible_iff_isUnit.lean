import Mathlib

variable {α : Type u}

theorem nonempty_invertible_iff_isUnit [Monoid α] (a : α) : Nonempty (Invertible a) ↔ IsUnit a := ⟨Nonempty.rec <| @isUnit_of_invertible _ _ _, IsUnit.nonempty_invertible⟩

