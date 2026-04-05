import Mathlib

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable (t : R) (x y z : L) (m n : M)

theorem lie_skew : -⁅y, x⁆ = ⁅x, y⁆ := by
  have h : ⁅x + y, x⁆ + ⁅x + y, y⁆ = 0 := by rw [← lie_add]; apply lie_self
  simpa [neg_eq_iff_add_eq_zero] using h

