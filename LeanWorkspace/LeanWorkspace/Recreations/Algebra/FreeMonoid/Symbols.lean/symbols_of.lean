import Mathlib

variable {α : Type*} [DecidableEq α]

theorem symbols_of {m : α} : FreeMonoid.symbols (of m) = {m} := rfl

