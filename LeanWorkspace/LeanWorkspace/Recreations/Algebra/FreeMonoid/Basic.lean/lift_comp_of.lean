import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem lift_comp_of (f : α → M) : FreeMonoid.lift f ∘ FreeMonoid.of = f := rfl

