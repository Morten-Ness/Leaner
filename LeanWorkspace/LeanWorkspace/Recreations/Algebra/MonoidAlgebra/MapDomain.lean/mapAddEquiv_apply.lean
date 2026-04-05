import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Mul M] [Mul N] [Mul O] [FunLike F M N] [MulHomClass F M N]

theorem mapAddEquiv_apply (e : R ≃+ S) (x : R[M]) (m : M) :
    MonoidAlgebra.mapAddEquiv M e x m = e (x m) := by simp [MonoidAlgebra.mapAddEquiv, MonoidAlgebra.map, coeff, ofCoeff]

