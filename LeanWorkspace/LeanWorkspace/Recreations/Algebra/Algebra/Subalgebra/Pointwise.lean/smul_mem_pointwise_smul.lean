import Mathlib

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

variable {R' : Type*} [Semiring R'] [MulSemiringAction R' A] [SMulCommClass R' R A]

theorem smul_mem_pointwise_smul (m : R') (r : A) (S : Subalgebra R A) : r ∈ S → m • r ∈ m • S := (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set A))

