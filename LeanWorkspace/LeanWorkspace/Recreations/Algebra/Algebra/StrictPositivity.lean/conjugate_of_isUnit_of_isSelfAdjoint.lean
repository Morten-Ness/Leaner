import Mathlib

variable {A : Type*}

variable [Semiring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]

theorem conjugate_of_isUnit_of_isSelfAdjoint (a b : A) (hb : IsUnit b)
    (hb₂ : IsSelfAdjoint b := by cfc_tac) (ha : IsStrictlyPositive a := by cfc_tac) :
    IsStrictlyPositive (b * a * b) :=
  (hb.isStrictlyPositive_iff_conjugate_of_isSelfAdjoint _ _ hb₂).mpr ha

