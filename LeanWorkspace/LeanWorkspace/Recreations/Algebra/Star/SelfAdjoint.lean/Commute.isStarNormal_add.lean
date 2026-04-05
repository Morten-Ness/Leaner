import Mathlib

variable {R A : Type*}

theorem Commute.isStarNormal_add [NonUnitalNonAssocSemiring R] [StarRing R] {a b : R}
    (hab : Commute a (star b)) [ha : IsStarNormal a] [hb : IsStarNormal b] :
    IsStarNormal (a + b) := by
  rw [isStarNormal_iff] at ha hb ⊢
  have := _root_.star_star b ▸ hab.star_star
  simp only [star_add, commute_iff_eq, mul_add, add_mul]
  rw [ha.eq, hb.eq, add_add_add_comm, hab.eq, this.eq]

