import Mathlib

variable {R S T A B C M N O : Type*}

theorem mapDomain_algebraMap {F : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [Monoid M] [Monoid N] [FunLike F M N] [MonoidHomClass F M N] (f : F) (r : R) :
    mapDomain f (algebraMap R A[M] r) = algebraMap R A[N] r := by
  simp only [MonoidAlgebra.coe_algebraMap, mapDomain_single, map_one, (· ∘ ·)]

