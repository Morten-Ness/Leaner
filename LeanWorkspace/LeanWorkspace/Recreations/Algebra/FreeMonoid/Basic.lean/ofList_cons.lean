import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem ofList_cons (x : α) (xs : List α) : FreeMonoid.ofList (x :: xs) = FreeMonoid.of x * FreeMonoid.ofList xs := rfl

