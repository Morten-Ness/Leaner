import Mathlib

theorem equivTuple_apply {R : Type*} (c₁ c₂ c₃ : R) (x : ℍ[R,c₁,c₂,c₃]) :
    QuaternionAlgebra.equivTuple c₁ c₂ c₃ x = ![x.re, x.imI, x.imJ, x.imK] := rfl

