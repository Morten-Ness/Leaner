import Mathlib

variable {α β : Type*} [Neg α]

theorem Even.const (b : β) : Function.Even (fun _ : α ↦ b) := fun _ ↦ rfl

