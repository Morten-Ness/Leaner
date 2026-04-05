import Mathlib

variable {α : Type u} [Mul α]

variable {β : Type v} [Semigroup β] (f : α →ₙ* β)

theorem lift_of (x : α) : Magma.AssocQuotient.lift f (Magma.AssocQuotient.of x) = f x := rfl

