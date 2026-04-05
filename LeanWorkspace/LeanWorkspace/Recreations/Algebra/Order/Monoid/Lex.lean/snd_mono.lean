import Mathlib

variable {α β : Type*} [Monoid α] [Preorder α] [Monoid β] [Preorder β]

theorem snd_mono : Monotone (MonoidHom.snd α β) := fun _ _ ↦ by simp +contextual [Prod.le_def]

