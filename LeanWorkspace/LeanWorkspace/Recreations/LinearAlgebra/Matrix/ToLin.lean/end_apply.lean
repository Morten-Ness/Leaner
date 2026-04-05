import Mathlib

variable {R M M₁ M₂ ι ι₁ ι₂ : Type*} [CommSemiring R]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [Module R M] [Module R M₁] [Module R M₂]

variable [Fintype ι] [Fintype ι₁] [Fintype ι₂]

variable [DecidableEq ι] [DecidableEq ι₁]

variable (b : Basis ι R M) (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂)

theorem end_apply (ij : ι × ι) : (b.end ij) = (Matrix.toLin b b) (Matrix.stdBasis R ι ι ij) := Module.Basis.linearMap_apply b b ij

