import Mathlib

variable {R : Type u}

variable [Mul R] [HasDistribNeg R] {a x y : R}

theorem neg_right (h : SemiconjBy a x y) : SemiconjBy a (-x) (-y) := by
  simp only [SemiconjBy, h.eq, neg_mul, mul_neg]

