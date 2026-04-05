import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {a : FreeMonoid α}

theorem length_mul (a b : FreeMonoid α) : (a * b).length = a.length + b.length := List.length_append

