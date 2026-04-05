import Mathlib

variable {Γ : Type*} [PartialOrder Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

variable {Γ Γ' : Type*} [PartialOrder Γ] [PartialOrder Γ'] {R : Type*}
  [CommRing R] {U V W : Type*} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ' R U V)

theorem coeff_comp (g : Γ' ×ₗ Γ) :
    (HVertexOperator.comp A B).coeff g = A.coeff (ofLex g).2 ∘ₗ B.coeff (ofLex g).1 := by
  rfl

