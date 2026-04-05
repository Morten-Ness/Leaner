import Mathlib

variable {R S A : Type*} [Field R] [Ring A] [Algebra R A]
  [SetLike S A] [hSA : NonUnitalSubringClass S A] [hSRA : SMulMemClass S R A] (s : S)

theorem unitization_injective (h1 : (1 : A) ∉ s) : Function.Injective (NonUnitalSubalgebra.unitization s) := AlgHomClass.unitization_injective s h1 (NonUnitalSubalgebra.unitization s) fun _ ↦ by simp

