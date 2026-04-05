import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem ofList_toList (xs : FreeMonoid α) : FreeMonoid.ofList (FreeMonoid.toList xs) = xs := rfl

