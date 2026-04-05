import Mathlib

theorem mk.eta {R : Type*} {c₁ c₂ c₃} (a : ℍ[R,c₁,c₂,c₃]) : QuaternionAlgebra.mk a.1 a.2 a.3 a.4 = a := rfl

