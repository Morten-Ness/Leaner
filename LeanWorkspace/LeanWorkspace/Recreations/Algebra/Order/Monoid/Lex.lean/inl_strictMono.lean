import Mathlib

variable {α β : Type*} [Monoid α] [Preorder α] [Monoid β] [Preorder β]

theorem inl_strictMono : StrictMono (MonoidHom.inl α β) := fun _ _ ↦ by simp

