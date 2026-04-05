import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {f : α → β} {a b : FreeMonoid α}

theorem lift_of_comp_eq_map (f : α → β) : (FreeMonoid.lift fun x ↦ FreeMonoid.of (f x)) = FreeMonoid.map f := FreeMonoid.hom_eq fun _ ↦ rfl

