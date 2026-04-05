import Mathlib

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem neg_eq' : Neg.neg = (id : R → R) := funext CharTwo.neg_eq

