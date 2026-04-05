import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem length_reverse {a : FreeMonoid α} : a.reverse.length = a.length := List.length_reverse

