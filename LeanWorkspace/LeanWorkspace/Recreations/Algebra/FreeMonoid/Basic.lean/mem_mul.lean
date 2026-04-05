import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {m : α}

theorem mem_mul {a b : FreeMonoid α} : m ∈ (a * b) ↔ m ∈ a ∨ m ∈ b := List.mem_append

