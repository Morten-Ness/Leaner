import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {f : α → β} {a b : FreeMonoid α}

theorem mem_map {m : β} : m ∈ FreeMonoid.map f a ↔ ∃ n ∈ a, f n = m := List.mem_map

