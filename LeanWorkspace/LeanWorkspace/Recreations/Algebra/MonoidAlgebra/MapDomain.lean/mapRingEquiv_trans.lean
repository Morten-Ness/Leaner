import Mathlib

variable {ι F R S T M N O : Type*}

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

variable [Monoid M] [Monoid N] [Monoid O]

theorem mapRingEquiv_trans (e₁ : R ≃+* S) (e₂ : S ≃+* T) :
    MonoidAlgebra.mapRingEquiv M (e₁.trans e₂) =
      (MonoidAlgebra.mapRingEquiv M e₁).trans (MonoidAlgebra.mapRingEquiv M e₂) := by ext; simp

