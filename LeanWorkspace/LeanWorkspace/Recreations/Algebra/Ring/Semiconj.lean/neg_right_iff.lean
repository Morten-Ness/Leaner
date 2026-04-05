import Mathlib

variable {R : Type u}

variable [Mul R] [HasDistribNeg R] {a x y : R}

theorem neg_right_iff : SemiconjBy a (-x) (-y) ↔ SemiconjBy a x y := ⟨fun h => neg_neg x ▸ neg_neg y ▸ SemiconjBy.neg_right h, SemiconjBy.neg_right⟩

