import Mathlib

variable {R M M₁ M₂ ι ι₁ ι₂ : Type*} [CommSemiring R]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [Module R M] [Module R M₁] [Module R M₂]

variable [Fintype ι] [Fintype ι₁] [Fintype ι₂]

variable [DecidableEq ι] [DecidableEq ι₁]

variable (b : Basis ι R M) (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂)

theorem linearMap_apply_apply (ij : ι₂ × ι₁) (k : ι₁) :
    (b₁.linearMap b₂ ij) (b₁ k) = if ij.2 = k then b₂ ij.1 else 0 := by
  have := Classical.decEq ι₂
  rw [Module.Basis.linearMap_apply, Matrix.stdBasis_eq_single, Matrix.toLin_self]
  dsimp only [Matrix.single, of_apply]
  simp_rw [ite_smul, one_smul, zero_smul, ite_and, Finset.sum_ite_eq, Finset.mem_univ, if_true]

