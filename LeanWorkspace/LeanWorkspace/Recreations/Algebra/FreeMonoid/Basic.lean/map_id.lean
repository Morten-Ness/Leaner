import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {f : α → β} {a b : FreeMonoid α}

theorem map_id : FreeMonoid.map (@id α) = MonoidHom.id (FreeMonoid α) := FreeMonoid.hom_eq fun _ ↦ rfl

