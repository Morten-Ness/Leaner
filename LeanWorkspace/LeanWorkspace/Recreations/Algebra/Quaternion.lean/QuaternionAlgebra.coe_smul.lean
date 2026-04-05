import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

theorem coe_smul [Zero R] [SMulZeroClass S R] (s : S) (r : R) :
    (↑(s • r) : ℍ[R,c₁,c₂,c₃]) = s • (r : ℍ[R,c₁,c₂,c₃]) := QuaternionAlgebra.ext rfl (smul_zero _).symm (smul_zero _).symm (smul_zero _).symm

