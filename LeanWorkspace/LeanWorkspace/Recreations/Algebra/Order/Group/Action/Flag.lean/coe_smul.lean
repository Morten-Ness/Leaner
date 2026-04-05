import Mathlib

open scoped Pointwise

variable {α : Type*}

variable [Preorder α]

theorem coe_smul (e : α ≃o α) (s : Flag α) : (↑(e • s) : Set α) = e • s := rfl

