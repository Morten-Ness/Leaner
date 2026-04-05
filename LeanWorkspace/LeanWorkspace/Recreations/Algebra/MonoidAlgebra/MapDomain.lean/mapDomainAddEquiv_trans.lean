import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Mul M] [Mul N] [Mul O] [FunLike F M N] [MulHomClass F M N]

theorem mapDomainAddEquiv_trans (e₁ : M ≃ N) (e₂ : N ≃ O) :
    MonoidAlgebra.mapDomainAddEquiv R (e₁.trans e₂) =
      (MonoidAlgebra.mapDomainAddEquiv R e₁).trans (MonoidAlgebra.mapDomainAddEquiv R e₂) := by ext; simp

