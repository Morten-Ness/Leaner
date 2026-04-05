import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [NonUnitalRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R] {p q : R}

theorem le_of_mul_eq_right (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hpq : q * p = p) : p ≤ q := sub_nonneg.mp (hp.sub_of_mul_eq_right hq hpq).nonneg

