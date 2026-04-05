import Mathlib

open scoped NNRat

variable {R A : Type*}

variable [Semiring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]

theorem IsUnit.star_right_conjugate_nonneg_iff {u x : R} (hu : IsUnit u) :
    0 ≤ u * x * star u ↔ 0 ≤ x := by
  refine ⟨fun h ↦ ?_, fun h ↦ star_right_conjugate_nonneg h _⟩
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have := by simpa [← mul_assoc] using star_right_conjugate_nonneg h v
  rwa [hv, one_mul, mul_assoc, ← star_mul, hv, star_one, mul_one] at this

