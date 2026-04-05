import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

variable [Semiring α] [Semiring β]

theorem isUnit_map (f : α →+* β) {a : α} : IsUnit a → IsUnit (f a) := IsUnit.map f

