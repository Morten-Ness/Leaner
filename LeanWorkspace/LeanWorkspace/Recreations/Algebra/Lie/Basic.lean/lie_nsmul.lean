import Mathlib

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable (t : R) (x y z : L) (m n : M)

theorem lie_nsmul (n : ℕ) : ⁅x, n • m⁆ = n • ⁅x, m⁆ := AddMonoidHom.map_nsmul
    { toFun := fun m : M => ⁅x, m⁆, map_zero' := lie_zero x, map_add' := fun _ _ => lie_add _ _ _ }
    _ _

