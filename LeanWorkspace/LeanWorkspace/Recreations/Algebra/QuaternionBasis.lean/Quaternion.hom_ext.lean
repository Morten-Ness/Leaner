import Mathlib

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

theorem hom_ext ⦃f g : ℍ[R] →ₐ[R] A⦄
    (hi : f (Basis.self R).i = g (Basis.self R).i) (hj : f (Basis.self R).j = g (Basis.self R).j) :
    f = g := QuaternionAlgebra.hom_ext hi hj

