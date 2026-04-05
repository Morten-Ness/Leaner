import Mathlib

variable {α : Type*}

theorem bot_eq [Preorder α] {a : α} : (⊥ : { x : α // a ≤ x }) = ⟨a, le_rfl⟩ := rfl

