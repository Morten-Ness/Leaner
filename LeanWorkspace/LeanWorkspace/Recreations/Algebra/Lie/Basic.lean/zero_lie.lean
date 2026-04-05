import Mathlib

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable (t : R) (x y z : L) (m n : M)

theorem zero_lie : ⁅(0 : L), m⁆ = 0 := (AddMonoidHom.mk' (fun x : L => ⁅x, m⁆) fun x y => add_lie x y m).map_zero

