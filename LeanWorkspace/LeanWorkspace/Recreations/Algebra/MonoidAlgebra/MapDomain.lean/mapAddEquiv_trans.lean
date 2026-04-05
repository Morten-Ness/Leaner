import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Mul M] [Mul N] [Mul O] [FunLike F M N] [MulHomClass F M N]

theorem mapAddEquiv_trans (e₁ : R ≃+ S) (e₂ : S ≃+ T) :
    MonoidAlgebra.mapAddEquiv M (e₁.trans e₂) = (MonoidAlgebra.mapAddEquiv M e₁).trans (MonoidAlgebra.mapAddEquiv M e₂) := by
  ext; simp

