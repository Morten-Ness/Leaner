import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

theorem le_max_triv_iff_bracket_eq_bot {N : LieSubmodule R L M} :
    N ≤ LieModule.maxTrivSubmodule R L M ↔ ⁅(⊤ : LieIdeal R L), N⁆ = ⊥ := by
  refine ⟨fun h => ?_, fun h m hm => ?_⟩
  · rw [← le_bot_iff, ← LieModule.ideal_oper_maxTrivSubmodule_eq_bot R L M ⊤]
    exact LieSubmodule.mono_lie_right ⊤ h
  · rw [LieModule.mem_maxTrivSubmodule]
    rw [LieSubmodule.lie_eq_bot_iff] at h
    exact fun x => h x (LieSubmodule.mem_top x) m hm

