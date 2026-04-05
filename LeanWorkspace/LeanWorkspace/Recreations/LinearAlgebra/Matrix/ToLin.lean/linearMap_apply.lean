import Mathlib

variable {R M M₁ M₂ ι ι₁ ι₂ : Type*} [CommSemiring R]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [Module R M] [Module R M₁] [Module R M₂]

variable [Fintype ι] [Fintype ι₁] [Fintype ι₂]

variable [DecidableEq ι] [DecidableEq ι₁]

variable (b : Basis ι R M) (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂)

theorem linearMap_apply (ij : ι₂ × ι₁) :
    (b₁.linearMap b₂ ij) = (Matrix.toLin b₁ b₂) (Matrix.stdBasis R ι₂ ι₁ ij) := by
  simp [Module.Basis.linearMap]

