import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α] [Monoid β]

theorem isConj_comm {g h : α} : IsConj g h ↔ IsConj h g := ⟨IsConj.symm, IsConj.symm⟩

