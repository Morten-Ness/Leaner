import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {a : FreeMonoid α}

theorem length_eq_three {v : FreeMonoid α} : v.length = 3 ↔ ∃ (a b c : α), v = FreeMonoid.of a * FreeMonoid.of b * FreeMonoid.of c := List.length_eq_three

