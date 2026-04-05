import Mathlib

variable {Γ : Type*} [PartialOrder Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem of_coeff_coeff (A : HVertexOperator Γ R V W) : HVertexOperator.of_coeff A.coeff A.coeff_isPWOsupport = A := rfl

