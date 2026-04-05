import Mathlib

variable {R : Type u}

variable [NonUnitalNonAssocRing R] {a b x y x' y' : R}

theorem sub_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x - x') (y - y') := by
  simpa only [sub_eq_add_neg] using SemiconjBy.add_right h SemiconjBy.neg_right h'

