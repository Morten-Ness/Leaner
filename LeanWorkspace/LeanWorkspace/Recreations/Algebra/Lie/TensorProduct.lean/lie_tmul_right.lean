import Mathlib

open scoped TensorProduct

variable {R : Type u} [CommRing R]

variable {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂} {Q : Type w₃}

variable [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable [AddCommGroup P] [Module R P] [LieRingModule L P] [LieModule R L P]

variable [AddCommGroup Q] [Module R Q] [LieRingModule L Q] [LieModule R L Q]

theorem lie_tmul_right (x : L) (m : M) (n : N) : ⁅x, m ⊗ₜ[R] n⁆ = ⁅x, m⁆ ⊗ₜ n + m ⊗ₜ ⁅x, n⁆ := show TensorProduct.LieModule.hasBracketAux x (m ⊗ₜ[R] n) = _ by
    simp only [TensorProduct.LieModule.hasBracketAux, LinearMap.rTensor_tmul, toEnd_apply_apply,
      LinearMap.add_apply, LinearMap.lTensor_tmul]

