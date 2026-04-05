import Mathlib

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]

variable {m : Type*} [Fintype m] [DecidableEq m] (b : Basis m R S)

theorem leftMulMatrix_apply (x : S) : Algebra.leftMulMatrix b x = LinearMap.toMatrix b b (lmul R S x) := rfl

