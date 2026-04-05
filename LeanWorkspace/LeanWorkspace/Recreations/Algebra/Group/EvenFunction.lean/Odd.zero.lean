import Mathlib

variable {α β : Type*} [Neg α]

theorem Odd.zero [NegZeroClass β] : Function.Odd (fun (_ : α) ↦ (0 : β)) := fun _ ↦ neg_zero.symm

