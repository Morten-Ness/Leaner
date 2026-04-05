import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Mul M] [Mul N] [Mul O] [FunLike F M N] [MulHomClass F M N]

theorem symm_mapAddEquiv (e : R ≃+ S) :
    (MonoidAlgebra.mapAddEquiv M e).symm = MonoidAlgebra.mapAddEquiv M e.symm := rfl

