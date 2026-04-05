import Mathlib

variable {R : Type*} [CommRing R]

variable {A : Type*} [CommRing A] [Algebra R A]

variable {L : Type*} [LieRing L] [LieAlgebra R L]

theorem ofDerivation_apply (d : Lie.Derivation R A A) (x : A ⊗[R] L) :
    Lie.Derivation.ofDerivation L d x = d.toLinearMap.rTensor L x := rfl

