import Mathlib

variable {R : Type u}

variable [Mul R] [HasDistribNeg R] {a b : R}

theorem neg_right_iff : Commute a (-b) ↔ Commute a b := SemiconjBy.neg_right_iff

