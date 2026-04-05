import Mathlib

open scoped TensorProduct

variable (R A L M : Type*)

variable [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

set_option backward.privateInPublic true in
private def bracket' : A ⊗[R] L →ₗ[A] A ⊗[R] M →ₗ[A] A ⊗[R] M := TensorProduct.curry <|
    TensorProduct.AlgebraTensorModule.map
        (LinearMap.mul' A A) (LieModule.toModuleHom R L M : L ⊗[R] M →ₗ[R] M) ∘ₗ
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R A A A L A M).toLinearMap


private theorem bracket'_tmul (s t : A) (x : L) (m : M) :
    bracket' R A L M (s ⊗ₜ[R] x) (t ⊗ₜ[R] m) = (s * t) ⊗ₜ ⁅x, m⁆ := rfl


set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
private theorem bracket_def (x : A ⊗[R] L) (m : A ⊗[R] M) : ⁅x, m⁆ = bracket' R A L M x m := rfl


theorem bracket_tmul (s t : A) (x : L) (y : M) : ⁅s ⊗ₜ[R] x, t ⊗ₜ[R] y⁆ = (s * t) ⊗ₜ ⁅x, y⁆ := rfl

