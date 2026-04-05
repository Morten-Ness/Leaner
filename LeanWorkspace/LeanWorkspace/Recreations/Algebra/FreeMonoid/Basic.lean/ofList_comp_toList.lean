import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem ofList_comp_toList : @FreeMonoid.ofList α ∘ FreeMonoid.toList = id := rfl

