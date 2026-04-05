import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {a : FreeMonoid α}

theorem length_eq_one : FreeMonoid.length a = 1 ↔ ∃ m, a = FreeMonoid.of m := List.length_eq_one_iff

