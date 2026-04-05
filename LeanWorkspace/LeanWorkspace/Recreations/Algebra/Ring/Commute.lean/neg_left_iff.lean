import Mathlib

variable {R : Type u}

variable [Mul R] [HasDistribNeg R] {a b : R}

theorem neg_left_iff : Commute (-a) b ↔ Commute a b := SemiconjBy.neg_left_iff

