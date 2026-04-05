import Mathlib

variable {α : Type u} {R : Type v}

variable [Mul α] [HasDistribNeg α]

theorem mul_neg (a b : α) : a * -b = -(a * b) := HasDistribNeg.mul_neg _ _

