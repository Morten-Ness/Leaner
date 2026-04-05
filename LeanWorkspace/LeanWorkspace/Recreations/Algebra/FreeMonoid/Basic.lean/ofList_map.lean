import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {f : α → β} {a b : FreeMonoid α}

theorem ofList_map (f : α → β) (xs : List α) : FreeMonoid.ofList (xs.map f) = FreeMonoid.map f (FreeMonoid.ofList xs) := rfl

