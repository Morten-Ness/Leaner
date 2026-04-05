import Mathlib

variable {α β : Type*} [Monoid α] [Preorder α] [Monoid β] [Preorder β]

theorem inr_mono : Monotone (MonoidHom.inr α β) := fun _ _ ↦ by simp

