import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [CommRing R]

theorem coe_basisOneIJK_repr (q : ℍ[R,c₁,c₂,c₃]) :
    ((QuaternionAlgebra.basisOneIJK c₁ c₂ c₃).repr q) = ![q.re, q.imI, q.imJ, q.imK] := rfl

