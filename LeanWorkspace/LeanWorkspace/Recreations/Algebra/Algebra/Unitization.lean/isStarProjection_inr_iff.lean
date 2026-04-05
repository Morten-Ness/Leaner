import Mathlib

theorem isStarProjection_inr_iff {R A : Type*} [Semiring R] [StarRing R] [NonUnitalSemiring A]
    [StarRing A] [Module R A] {p : A} :
    IsStarProjection (p : Unitization R A) ↔ IsStarProjection p := by
  simp [isStarProjection_iff]

protected alias ⟨_root_.IsStarProjection.of_inr, _root_.IsStarProjection.inr⟩ :=
  isStarProjection_inr_iff

