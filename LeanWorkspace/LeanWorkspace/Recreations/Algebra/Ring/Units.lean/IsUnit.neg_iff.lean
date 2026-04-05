import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

theorem IsUnit.neg_iff [Monoid α] [HasDistribNeg α] (a : α) : IsUnit (-a) ↔ IsUnit a := ⟨fun h => neg_neg a ▸ h.neg, IsUnit.neg⟩

