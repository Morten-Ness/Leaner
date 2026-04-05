import Mathlib

variable {α : Type u} {β : Type v}

variable [Group α]

theorem conj_injective {x : α} : Function.Injective fun g : α => x * g * x⁻¹ := fun a b ↦ by simp

