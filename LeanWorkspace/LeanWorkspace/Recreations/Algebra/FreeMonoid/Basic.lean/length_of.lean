import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {a : FreeMonoid α}

theorem length_of (m : α) : FreeMonoid.length (FreeMonoid.of m) = 1 := rfl

