import Mathlib

variable {R L M M' : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup M'] [Module R M'] [LieRingModule L M'] [LieModule R L M']

variable (H : LieSubalgebra R L)

theorem normalizer_eq_self_iff :
    H.normalizer = H ↔ (LieModule.maxTrivSubmodule R H <| L ⧸ H.toLieSubmodule) = ⊥ := by
  rw [LieSubmodule.eq_bot_iff]
  refine ⟨fun h => ?_, fun h => le_antisymm ?_ H.le_normalizer⟩
  · rintro ⟨x⟩ hx
    suffices x ∈ H by rwa [Submodule.Quotient.quot_mk_eq_mk, Submodule.Quotient.mk_eq_zero,
      coe_toLieSubmodule, mem_toSubmodule]
    rw [← h, H.mem_normalizer_iff']
    intro y hy
    replace hx : ⁅_, LieSubmodule.Quotient.mk' _ x⁆ = 0 := hx ⟨y, hy⟩
    rwa [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk_eq_zero] at hx
  · intro x hx
    let y := LieSubmodule.Quotient.mk' H.toLieSubmodule x
    have hy : y ∈ LieModule.maxTrivSubmodule R H (L ⧸ H.toLieSubmodule) := by
      rintro ⟨z, hz⟩
      rw [← LieModuleHom.map_lie, LieSubmodule.Quotient.mk_eq_zero, coe_bracket_of_module,
        Submodule.coe_mk, mem_toLieSubmodule]
      exact (H.mem_normalizer_iff' x).mp hx z hz
    simpa [y] using h y hy

