import Mathlib

variable {R : Type u}

theorem add_left [Distrib R] {a b x y : R} (ha : SemiconjBy a x y) (hb : SemiconjBy b x y) :
    SemiconjBy (a + b) x y := by
  simp only [SemiconjBy, left_distrib, right_distrib, ha.eq, hb.eq]

