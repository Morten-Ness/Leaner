import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem reverse_of (a : α) : FreeMonoid.reverse (FreeMonoid.of a) = FreeMonoid.of a := rfl

