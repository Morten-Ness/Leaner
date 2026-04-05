import Mathlib

variable {α β : Type*} [Monoid α] [Preorder α] [Monoid β] [Preorder β]

theorem fst_mono : Monotone (MonoidHom.fst α β) := fun _ _ ↦ by simp +contextual [Prod.le_def]

