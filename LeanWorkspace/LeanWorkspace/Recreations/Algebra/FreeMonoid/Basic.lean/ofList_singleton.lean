import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem ofList_singleton (x : α) : FreeMonoid.ofList [x] = FreeMonoid.of x := rfl

