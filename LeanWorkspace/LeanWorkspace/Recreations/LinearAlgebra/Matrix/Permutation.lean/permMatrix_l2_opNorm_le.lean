import Mathlib

open scoped Matrix.Norms.L2Operator

variable {n R : Type*} [DecidableEq n] (σ τ : Perm n)

variable [Fintype n]

variable {𝕜 : Type*} [RCLike 𝕜]

theorem permMatrix_l2_opNorm_le : ‖σ.permMatrix 𝕜‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ (by simp) <| by
    simp [EuclideanSpace.norm_eq, toLpLin_apply, Matrix.permMatrix_mulVec,
      σ.sum_comp _ (fun i ↦ ‖_‖ ^ 2)]

