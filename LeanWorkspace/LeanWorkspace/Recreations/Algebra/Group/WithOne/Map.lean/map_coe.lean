import Mathlib

variable {α β γ : Type*}

theorem map_coe (f : α → β) (a : α) : WithOne.map f a = f a := rfl

