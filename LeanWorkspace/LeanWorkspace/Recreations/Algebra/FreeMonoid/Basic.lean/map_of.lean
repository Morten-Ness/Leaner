import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {f : α → β} {a b : FreeMonoid α}

theorem map_of (f : α → β) (x : α) : FreeMonoid.map f (FreeMonoid.of x) = FreeMonoid.of (f x) := rfl

