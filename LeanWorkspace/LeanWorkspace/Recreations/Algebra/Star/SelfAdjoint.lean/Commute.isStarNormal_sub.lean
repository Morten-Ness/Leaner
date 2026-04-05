import Mathlib

variable {R A : Type*}

theorem Commute.isStarNormal_sub [NonUnitalNonAssocRing R] [StarRing R] {a b : R}
    (hab : Commute a (star b)) [ha : IsStarNormal a] [hb : IsStarNormal b] :
    IsStarNormal (a - b) := sub_eq_add_neg a b ▸ (star_neg b ▸ hab.neg_right).isStarNormal_add

