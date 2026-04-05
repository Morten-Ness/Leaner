import Mathlib

variable {α : Type*} [DecidableEq α]

theorem mem_symbols {m : α} {a : FreeMonoid α} : m ∈ FreeMonoid.symbols a ↔ m ∈ a := List.mem_toFinset

