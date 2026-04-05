import Mathlib

variable {Γ : Type*} [PartialOrder Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem ext (A B : HVertexOperator Γ R V W) (h : ∀ v : V, A v = B v) :
    A = B := LinearMap.ext h

