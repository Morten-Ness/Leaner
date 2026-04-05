import Mathlib

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable (t : R) (x y z : L) (m n : M)

theorem nsmul_lie (n : ℕ) : ⁅n • x, m⁆ = n • ⁅x, m⁆ := AddMonoidHom.map_nsmul
    { toFun := fun x : L => ⁅x, m⁆, map_zero' := zero_lie m, map_add' := fun _ _ => add_lie _ _ _ }
    _ _

