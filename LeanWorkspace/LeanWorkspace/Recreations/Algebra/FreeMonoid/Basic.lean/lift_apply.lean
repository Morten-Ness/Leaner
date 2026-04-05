import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem lift_apply (f : α → M) (l : FreeMonoid α) : FreeMonoid.lift f l = ((FreeMonoid.toList l).map f).prod := FreeMonoid.prodAux_eq _

