import Mathlib

variable {α : Type u} {R : Type v}

variable [Mul α] [HasDistribNeg α]

theorem neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b := (neg_mul _ _).symm

