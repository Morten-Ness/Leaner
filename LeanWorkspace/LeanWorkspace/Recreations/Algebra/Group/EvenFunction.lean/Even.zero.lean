import Mathlib

variable {α β : Type*} [Neg α]

theorem Even.zero [Zero β] : Function.Even (fun (_ : α) ↦ (0 : β)) := Function.Even.const 0

