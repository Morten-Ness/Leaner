import Mathlib

variable {R : Type*} [CommRing R]

variable {A : Type*} [CommRing A] [Algebra R A]

variable {L : Type*} [LieRing L] [LieAlgebra R L]

theorem ofLieDerivation_apply (d : LieDerivation R L L) (x : A ⊗[R] L) :
    Lie.Derivation.ofLieDerivation A d x = d.toLinearMap.lTensor A x := rfl

