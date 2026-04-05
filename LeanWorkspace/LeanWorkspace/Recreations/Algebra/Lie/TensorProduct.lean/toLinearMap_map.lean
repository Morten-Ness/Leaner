import Mathlib

open scoped TensorProduct

variable {R : Type u} [CommRing R]

variable {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂} {Q : Type w₃}

variable [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable [AddCommGroup P] [Module R P] [LieRingModule L P] [LieModule R L P]

variable [AddCommGroup Q] [Module R Q] [LieRingModule L Q] [LieModule R L Q]

theorem toLinearMap_map (f : M →ₗ⁅R,L⁆ P) (g : N →ₗ⁅R,L⁆ Q) :
    (map f g : M ⊗[R] N →ₗ[R] P ⊗[R] Q) = TensorProduct.map (f : M →ₗ[R] P) (g : N →ₗ[R] Q) := rfl

