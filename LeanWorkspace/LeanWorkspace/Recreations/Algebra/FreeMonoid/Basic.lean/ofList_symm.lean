import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem ofList_symm : (@FreeMonoid.ofList α).symm = FreeMonoid.toList := rfl

