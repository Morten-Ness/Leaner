import Mathlib

variable {R S A : Type*} [Field R] [StarRing R] [Ring A] [StarRing A] [Algebra R A]
  [StarModule R A] [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A]
  [StarMemClass S A] (s : S)

theorem unitization_injective (h1 : (1 : A) ∉ s) : Function.Injective (NonUnitalStarSubalgebra.unitization s) := AlgHomClass.unitization_injective s h1 (NonUnitalStarSubalgebra.unitization s) fun _ ↦ by simp

