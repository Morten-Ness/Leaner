import Mathlib

variable {R M M₁ M₂ ι ι₁ ι₂ : Type*} [CommSemiring R]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [Module R M] [Module R M₁] [Module R M₂]

variable [Fintype ι] [Fintype ι₁] [Fintype ι₂]

variable [DecidableEq ι] [DecidableEq ι₁]

variable (b : Basis ι R M) (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂)

theorem end_apply_apply (ij : ι × ι) (k : ι) : (b.end ij) (b k) = if ij.2 = k then b ij.1 else 0 := Module.Basis.linearMap_apply_apply b b ij k

