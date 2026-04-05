import Mathlib

variable {α : Type u} {R : Type v}

variable [Mul α] [HasDistribNeg α]

theorem neg_mul (a b : α) : -a * b = -(a * b) := HasDistribNeg.neg_mul _ _

