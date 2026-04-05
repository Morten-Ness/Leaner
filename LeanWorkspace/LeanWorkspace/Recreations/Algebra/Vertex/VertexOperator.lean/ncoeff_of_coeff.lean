import Mathlib

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem ncoeff_of_coeff (f : ℤ → Module.End R V)
    (hf : ∀ x, BddBelow (Function.support fun y ↦ f y x)) (n : ℤ) :
    (VertexOperator.of_coeff f hf)[[n]] = f (-n - 1) := by
  ext v
  rw [VertexOperator.ncoeff_apply, coeff_apply_apply, VertexOperator.of_coeff_apply_coeff]

