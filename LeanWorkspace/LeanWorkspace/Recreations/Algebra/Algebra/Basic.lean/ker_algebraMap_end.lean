import Mathlib

open scoped Algebra

variable (R : Type u) (S : Type v) (M : Type w)

variable [CommSemiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]

variable [SMulCommClass S R M] [SMul R S] [IsScalarTower R S M]

theorem ker_algebraMap_end (K : Type u) (V : Type v) [Semifield K] [AddCommMonoid V] [Module K V]
    (a : K) (ha : a ≠ 0) : LinearMap.ker ((algebraMap K (End K V)) a) = ⊥ := LinearMap.ker_smul _ _ ha

