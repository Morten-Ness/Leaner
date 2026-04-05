import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Mul M] [Mul N] [Mul O] [FunLike F M N] [MulHomClass F M N]

theorem mapDomainAddEquiv_apply (e : M ≃ N) (x : R[M]) (n : N) :
    MonoidAlgebra.mapDomainAddEquiv R e x n = x (e.symm n) := by simp [MonoidAlgebra.mapDomainAddEquiv]

