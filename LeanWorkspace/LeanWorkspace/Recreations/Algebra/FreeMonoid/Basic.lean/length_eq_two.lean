import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {a : FreeMonoid α}

theorem length_eq_two {v : FreeMonoid α} :
    v.length = 2 ↔ ∃ c d, v = FreeMonoid.of c * FreeMonoid.of d := List.length_eq_two

