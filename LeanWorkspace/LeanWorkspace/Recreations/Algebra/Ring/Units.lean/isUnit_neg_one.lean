import Mathlib

variable {α : Type u} {β : Type v} {R : Type x}

theorem isUnit_neg_one [Monoid α] [HasDistribNeg α] : IsUnit (-1 : α) := isUnit_one.neg

