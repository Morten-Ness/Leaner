import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {α β : Type*}

theorem freeMonoidCongr_of (e : α ≃ β) (a : α) : FreeMonoid.freeMonoidCongr e (FreeMonoid.of a) = FreeMonoid.of (e a) := rfl

