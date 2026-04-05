import Mathlib

variable {α : Type*}

variable [CommMonoid α] {x y z : α}

theorem symmetric_isRelPrime : Symmetric (IsRelPrime : α → α → Prop) := fun _ _ ↦ .symm

