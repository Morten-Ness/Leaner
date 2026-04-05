import Mathlib

variable {A : Type*}

variable [Semiring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]

theorem _root_.IsUnit.isStrictlyPositive_iff_conjugate_of_isSelfAdjoint (a b : A) (hb : IsUnit b)
    (hb₂ : IsSelfAdjoint b := by cfc_tac) :
    IsStrictlyPositive (b * a * b) ↔ IsStrictlyPositive a := by
  grind [hb.isStrictlyPositive_star_left_conjugate_iff]

