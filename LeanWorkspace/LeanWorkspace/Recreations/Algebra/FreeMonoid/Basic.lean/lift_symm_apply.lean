import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem lift_symm_apply (f : FreeMonoid α →* M) : FreeMonoid.lift.symm f = f ∘ FreeMonoid.of := rfl

