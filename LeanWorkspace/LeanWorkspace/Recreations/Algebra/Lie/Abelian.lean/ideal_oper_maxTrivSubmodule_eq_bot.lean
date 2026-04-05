import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

theorem ideal_oper_maxTrivSubmodule_eq_bot (I : LieIdeal R L) :
    ⁅I, LieModule.maxTrivSubmodule R L M⁆ = ⊥ := by
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.lieIdeal_oper_eq_linear_span,
    LieSubmodule.bot_toSubmodule, Submodule.span_eq_bot]
  rintro m ⟨⟨x, hx⟩, ⟨⟨m, hm⟩, rfl⟩⟩
  exact hm x

