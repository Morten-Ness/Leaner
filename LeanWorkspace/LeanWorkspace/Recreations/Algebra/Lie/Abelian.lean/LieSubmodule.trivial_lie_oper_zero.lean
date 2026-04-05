import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] (N N' : LieSubmodule R L M) (I J : LieIdeal R L)

theorem LieSubmodule.trivial_lie_oper_zero [LieModule.IsTrivial L M] : ⁅I, N⁆ = ⊥ := by
  suffices ⁅I, N⁆ ≤ ⊥ from le_bot_iff.mp this
  rw [lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le]
  rintro m ⟨x, n, h⟩; rw [trivial_lie_zero] at h; simp [← h]

