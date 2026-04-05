import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem lift_restrict (f : FreeMonoid α →* M) : FreeMonoid.lift (f ∘ FreeMonoid.of) = f := FreeMonoid.lift.apply_symm_apply f

