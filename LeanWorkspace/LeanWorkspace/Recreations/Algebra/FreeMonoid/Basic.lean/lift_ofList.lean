import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem lift_ofList (f : α → M) (l : List α) : FreeMonoid.lift f (FreeMonoid.ofList l) = (l.map f).prod := FreeMonoid.prodAux_eq _

