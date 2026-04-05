import Mathlib

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]

variable {m : Type*} [Fintype m] [DecidableEq m] (b : Basis m R S)

theorem toMatrix_lsmul (x : R) :
    LinearMap.toMatrix b b (Algebra.lsmul R R S x) = Matrix.diagonal fun _ ↦ x := toMatrix_distrib_mul_action_toLinearMap b x

