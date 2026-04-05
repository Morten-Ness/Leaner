import Mathlib

variable {α : Type u} [Mul α]

variable {β : Type v} [Mul β] (f : α →ₙ* β)

theorem map_of (x) : Magma.AssocQuotient.map f (Magma.AssocQuotient.of x) = Magma.AssocQuotient.of (f x) := rfl

