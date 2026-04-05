import Mathlib

variable {ι R M σ : Type*}

variable [DecidableEq ι] [AddCommMonoid M]

variable [SetLike σ M] [AddSubmonoidClass σ M] (ℳ : ι → σ)

variable [Decomposition ℳ]

theorem sum_support_decompose [∀ (i) (x : ℳ i), Decidable (x ≠ 0)] (r : M) :
    (∑ i ∈ (DirectSum.decompose ℳ r).support, (DirectSum.decompose ℳ r i : M)) = r := by
  conv_rhs =>
    rw [← (DirectSum.decompose ℳ).symm_apply_apply r, ← sum_support_of (DirectSum.decompose ℳ r)]
  rw [DirectSum.decompose_symm_sum]
  simp_rw [DirectSum.decompose_symm_of]

