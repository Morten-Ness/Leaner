import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {a : FreeMonoid α}

theorem length_eq_zero : FreeMonoid.length a = 0 ↔ a = 1 := List.length_eq_zero_iff

