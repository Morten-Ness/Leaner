import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Mul M] [Mul N] [Mul O] [FunLike F M N] [MulHomClass F M N]

theorem mapAddEquiv_single (e : R ≃+ S) (r : R) (m : M) :
    MonoidAlgebra.mapAddEquiv M e (single m r) = single m (e r) := by simp [MonoidAlgebra.mapAddEquiv]

