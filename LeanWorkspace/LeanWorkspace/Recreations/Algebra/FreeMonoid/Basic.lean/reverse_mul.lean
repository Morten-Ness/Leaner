import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem reverse_mul {a b : FreeMonoid α} : FreeMonoid.reverse (a * b) = FreeMonoid.reverse b * FreeMonoid.reverse a := List.reverse_append

