import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem coe_smul [SMulZeroClass S R] (s : S) (r : R) : (↑(s • r) : ℍ[R]) = s • (r : ℍ[R]) := QuaternionAlgebra.coe_smul _ _

