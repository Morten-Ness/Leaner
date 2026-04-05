import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {α β : Type*}

theorem freeMonoidCongr_symm_of (e : α ≃ β) (b : β) :
    FreeMonoid.freeMonoidCongr e.symm (FreeMonoid.of b) = FreeMonoid.of (e.symm b) := rfl

