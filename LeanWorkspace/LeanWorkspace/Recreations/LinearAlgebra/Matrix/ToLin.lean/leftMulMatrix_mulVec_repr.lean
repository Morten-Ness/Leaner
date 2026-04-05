import Mathlib

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]

variable {m : Type*} [Fintype m] [DecidableEq m] (b : Basis m R S)

theorem leftMulMatrix_mulVec_repr (x y : S) :
    Algebra.leftMulMatrix b x *ᵥ b.repr y = b.repr (x * y) := (LinearMap.mulLeft R x).toMatrix_mulVec_repr b b y

