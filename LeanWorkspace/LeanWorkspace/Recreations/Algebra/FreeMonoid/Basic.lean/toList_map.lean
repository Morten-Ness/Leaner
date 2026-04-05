import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {f : α → β} {a b : FreeMonoid α}

theorem toList_map (f : α → β) (xs : FreeMonoid α) : FreeMonoid.toList (FreeMonoid.map f xs) = xs.toList.map f := rfl

