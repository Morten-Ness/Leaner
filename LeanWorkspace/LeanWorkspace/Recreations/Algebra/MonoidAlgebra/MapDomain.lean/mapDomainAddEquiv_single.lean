import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Mul M] [Mul N] [Mul O] [FunLike F M N] [MulHomClass F M N]

theorem mapDomainAddEquiv_single (e : M ≃ N) (r : R) (m : M) :
    MonoidAlgebra.mapDomainAddEquiv R e (single m r) = single (e m) r := by simp [MonoidAlgebra.mapDomainAddEquiv]

