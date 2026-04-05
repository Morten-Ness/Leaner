import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S M : Type*}

variable [Semiring R] [Semiring S]

theorem liftNC_smul [AddZeroClass M] (f : S →+* R) (g : Multiplicative M →* R) (c : S) (φ : S[M]) :
    liftNC (f : S →+ R) g (c • φ) = f c * liftNC (f : S →+ R) g φ := by
  suffices (liftNC (↑f) g).comp (smulAddHom S S[M] c) =
      (AddMonoidHom.mulLeft (f c)).comp (liftNC f g) from DFunLike.congr_fun this φ
  ext
  simp_rw [AddMonoidHom.comp_apply, singleAddHom_apply, smulAddHom_apply,
    AddMonoidHom.coe_mulLeft, smul_single', liftNC_single, AddMonoidHom.coe_coe, map_mul, mul_assoc]

