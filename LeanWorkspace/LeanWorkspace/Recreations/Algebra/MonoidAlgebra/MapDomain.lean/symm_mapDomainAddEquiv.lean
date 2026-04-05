import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Mul M] [Mul N] [Mul O] [FunLike F M N] [MulHomClass F M N]

theorem symm_mapDomainAddEquiv (e : M ≃ N) :
    (MonoidAlgebra.mapDomainAddEquiv R e).symm = MonoidAlgebra.mapDomainAddEquiv R e.symm := rfl

