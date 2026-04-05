import Mathlib

variable {R : Type u}

variable [NonUnitalNonAssocRing R] {a b x y x' y' : R}

theorem sub_left (ha : SemiconjBy a x y) (hb : SemiconjBy b x y) :
    SemiconjBy (a - b) x y := by
  simpa only [sub_eq_add_neg] using SemiconjBy.add_left ha SemiconjBy.neg_left hb

