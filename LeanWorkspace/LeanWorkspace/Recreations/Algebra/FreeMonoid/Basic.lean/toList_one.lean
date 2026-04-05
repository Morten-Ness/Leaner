import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem toList_one : FreeMonoid.toList (1 : FreeMonoid α) = [] := rfl

