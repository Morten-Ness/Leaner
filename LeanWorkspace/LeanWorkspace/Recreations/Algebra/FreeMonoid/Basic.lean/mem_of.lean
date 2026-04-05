import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {m : α}

theorem mem_of {n : α} : m ∈ FreeMonoid.of n ↔ m = n := List.mem_singleton

