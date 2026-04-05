import Mathlib

variable {α : Type*} [DecidableEq α]

theorem symbols_one : FreeMonoid.symbols (1 : FreeMonoid α) = ∅ := rfl

