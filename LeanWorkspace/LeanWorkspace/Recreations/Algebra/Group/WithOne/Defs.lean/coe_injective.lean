import Mathlib

variable {α : Type u}

theorem coe_injective : Function.Injective (WithOne.coe : α → WithOne α) := Option.some_injective _

