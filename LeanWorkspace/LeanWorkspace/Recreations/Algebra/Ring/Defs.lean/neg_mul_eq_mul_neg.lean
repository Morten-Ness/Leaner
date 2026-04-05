import Mathlib

variable {α : Type u} {R : Type v}

variable [Mul α] [HasDistribNeg α]

theorem neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b := (mul_neg _ _).symm

