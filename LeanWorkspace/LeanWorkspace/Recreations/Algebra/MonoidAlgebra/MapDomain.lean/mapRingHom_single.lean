import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Monoid M] [Monoid N] [Monoid O]

theorem mapRingHom_single (f : R →+* S) (a : M) (b : R) :
    MonoidAlgebra.mapRingHom M f (single a b) = single a (f b) := by
  classical ext; simp [single_apply, apply_ite f]

