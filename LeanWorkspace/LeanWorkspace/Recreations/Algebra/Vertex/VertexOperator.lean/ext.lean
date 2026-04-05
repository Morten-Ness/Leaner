import Mathlib

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem ext (A B : VertexOperator R V) (h : ∀ v : V, A v = B v) :
    A = B := LinearMap.ext h

