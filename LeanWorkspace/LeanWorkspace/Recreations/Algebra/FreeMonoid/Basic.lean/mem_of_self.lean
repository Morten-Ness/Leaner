import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {m : α}

theorem mem_of_self : m ∈ FreeMonoid.of m := List.mem_singleton_self _

