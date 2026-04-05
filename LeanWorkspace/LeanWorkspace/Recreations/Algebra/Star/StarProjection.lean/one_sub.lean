import Mathlib

variable {R : Type*}

variable {p q : R}

variable [NonAssocRing R]

theorem one_sub [StarRing R] (hp : IsStarProjection p) : IsStarProjection (1 - p) where
  isIdempotentElem := hp.isIdempotentElem.one_sub
  isSelfAdjoint := .sub (.one _) hp.isSelfAdjoint

