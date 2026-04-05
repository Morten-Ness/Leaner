import Mathlib

variable {R : Type u}

variable [Mul R] [HasDistribNeg R] {a x y : R}

theorem neg_left_iff : SemiconjBy (-a) x y ↔ SemiconjBy a x y := ⟨fun h => neg_neg a ▸ SemiconjBy.neg_left h, SemiconjBy.neg_left⟩

