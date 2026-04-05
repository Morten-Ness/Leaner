import Mathlib

variable {R : Type*}

variable {p q : R}

theorem sub_iff_mul_eq_right [NonUnitalRing R] [StarRing R] [IsAddTorsionFree R]
    {p q : R} (hp : IsStarProjection p) (hq : IsStarProjection q) :
    IsStarProjection (q - p) ↔ q * p = p := by
  rw [← star_inj]
  simp [star_mul, hp.isSelfAdjoint.star_eq, hq.isSelfAdjoint.star_eq,
    IsStarProjection.sub_iff_mul_eq_left hp hq]

