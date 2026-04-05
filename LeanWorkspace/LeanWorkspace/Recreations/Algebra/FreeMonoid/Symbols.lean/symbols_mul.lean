import Mathlib

variable {α : Type*} [DecidableEq α]

theorem symbols_mul {a b : FreeMonoid α} : FreeMonoid.symbols (a * b) = FreeMonoid.symbols a ∪ FreeMonoid.symbols b := List.toFinset_append

