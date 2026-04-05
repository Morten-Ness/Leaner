import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem toList_cons (x : α) (xs : FreeMonoid α) : FreeMonoid.toList (x :: xs) = x :: FreeMonoid.toList xs := rfl

