import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {a : FreeMonoid α}

theorem length_eq_four {v : FreeMonoid α} :
    v.length = 4 ↔ ∃ (a b c d : α), v = FreeMonoid.of a * FreeMonoid.of b * FreeMonoid.of c * FreeMonoid.of d := List.length_eq_four

