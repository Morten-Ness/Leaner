import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {a : FreeMonoid α}

theorem one_ne_of (a : α) : 1 ≠ FreeMonoid.of a := FreeMonoid.of_ne_one _ |>.symm

