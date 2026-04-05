import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

theorem mapDomain_one [One M] [One N] {F : Type*} [FunLike F M N] [OneHomClass F M N] (f : F) :
    mapDomain f (1 : R[M]) = (1 : R[N]) := by
  simp [one_def]

