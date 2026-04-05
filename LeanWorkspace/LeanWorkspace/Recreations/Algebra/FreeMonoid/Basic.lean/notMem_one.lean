import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

variable {m : α}

theorem notMem_one : m ∉ (1 : FreeMonoid α) := List.not_mem_nil

