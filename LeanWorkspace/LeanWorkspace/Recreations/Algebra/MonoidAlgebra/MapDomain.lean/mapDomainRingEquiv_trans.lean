import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Monoid M] [Monoid N] [Monoid O]

theorem mapDomainRingEquiv_trans (e₁ : M ≃* N) (e₂ : N ≃* O) :
    MonoidAlgebra.mapDomainRingEquiv R (e₁.trans e₂) =
      (MonoidAlgebra.mapDomainRingEquiv R e₁).trans (MonoidAlgebra.mapDomainRingEquiv R e₂) := by ext; simp

