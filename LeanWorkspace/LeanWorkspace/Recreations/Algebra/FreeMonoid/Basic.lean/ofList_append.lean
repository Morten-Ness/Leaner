import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem ofList_append (xs ys : List α) : FreeMonoid.ofList (xs ++ ys) = FreeMonoid.ofList xs * FreeMonoid.ofList ys := rfl

