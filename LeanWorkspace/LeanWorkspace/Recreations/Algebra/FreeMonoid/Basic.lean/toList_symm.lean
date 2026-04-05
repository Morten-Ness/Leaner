import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem toList_symm : (@FreeMonoid.toList α).symm = FreeMonoid.ofList := rfl

