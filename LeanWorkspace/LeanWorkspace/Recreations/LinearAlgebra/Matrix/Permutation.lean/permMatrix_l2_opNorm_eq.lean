import Mathlib

open scoped Matrix.Norms.L2Operator

variable {n R : Type*} [DecidableEq n] (σ τ : Perm n)

variable [Fintype n]

variable {𝕜 : Type*} [RCLike 𝕜]

theorem permMatrix_l2_opNorm_eq [Nonempty n] : ‖σ.permMatrix 𝕜‖ = 1 := le_antisymm (Matrix.permMatrix_l2_opNorm_le σ) <| by
    inhabit n
    simpa [EuclideanSpace.norm_eq, Matrix.permMatrix_mulVec, ← Equiv.eq_symm_apply, apply_ite] using
      (σ.permMatrix 𝕜).l2_opNorm_mulVec (WithLp.toLp _ (Pi.single default 1))

