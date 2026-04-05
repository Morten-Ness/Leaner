import Mathlib

open scoped Pointwise Ring

variable {𝕜 : Type u} {A : Type v}

variable [Field 𝕜] [Ring A] [Algebra 𝕜 A]

theorem one_eq [Nontrivial A] : σ (1 : A) = {1} := calc
    σ (1 : A) = σ (↑ₐ 1) := by rw [Algebra.algebraMap_eq_smul_one, one_smul]
    _ = {1} := spectrum.scalar_eq 1

