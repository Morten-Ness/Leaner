import Mathlib

variable {Γ : Type*} [PartialOrder Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem coeff_of_coeff (f : Γ → V →ₗ[R] W)
    (hf : ∀ (x : V), (Function.support (fun g => f g x)).IsPWO) : (HVertexOperator.of_coeff f hf).coeff = f := rfl

