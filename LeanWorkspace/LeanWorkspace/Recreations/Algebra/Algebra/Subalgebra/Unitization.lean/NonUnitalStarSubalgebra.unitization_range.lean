import Mathlib

variable {R S A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]
  [StarModule R A] [SetLike S A] [hSA : NonUnitalSubsemiringClass S A] [hSRA : SMulMemClass S R A]
  [StarMemClass S A] (s : S)

theorem unitization_range : (NonUnitalStarSubalgebra.unitization s).range = StarAlgebra.adjoin R s := by
  rw [NonUnitalStarSubalgebra.unitization, Unitization.starLift_range]
  simp only [NonUnitalStarAlgHom.coe_range, NonUnitalStarSubalgebraClass.coe_subtype,
    Subtype.range_coe_subtype]
  rfl

