import Mathlib

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem of_coeff_apply_coeff (f : ℤ → Module.End R V)
    (hf : ∀ x, BddBelow (Function.support fun y ↦ f y x)) (x : V) (n : ℤ) :
    ((HahnModule.of R).symm ((VertexOperator.of_coeff f hf) x)).coeff n = (f n) x := by
  rfl

