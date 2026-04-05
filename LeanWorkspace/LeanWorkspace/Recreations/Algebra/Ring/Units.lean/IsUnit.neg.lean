import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

theorem IsUnit.neg [Monoid α] [HasDistribNeg α] {a : α} : IsUnit a → IsUnit (-a)
  | ⟨x, hx⟩ => hx ▸ (-x).isUnit
