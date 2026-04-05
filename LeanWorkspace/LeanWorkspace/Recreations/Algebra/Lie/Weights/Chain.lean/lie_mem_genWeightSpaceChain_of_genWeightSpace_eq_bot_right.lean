import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {H : LieSubalgebra R L} (α χ : H → R) (p q : ℤ)

theorem lie_mem_genWeightSpaceChain_of_genWeightSpace_eq_bot_right [LieRing.IsNilpotent H]
    (hq : genWeightSpace M (q • α + χ) = ⊥)
    {x : L} (hx : x ∈ rootSpace H α)
    {y : M} (hy : y ∈ LieModule.genWeightSpaceChain M α χ p q) :
    ⁅x, y⁆ ∈ LieModule.genWeightSpaceChain M α χ p q := by
  rw [LieModule.genWeightSpaceChain, iSup_subtype'] at hy
  induction hy using LieSubmodule.iSup_induction' with
  | mem k z hz =>
    obtain ⟨k, hk⟩ := k
    suffices genWeightSpace M ((k + 1) • α + χ) ≤ LieModule.genWeightSpaceChain M α χ p q by
      apply this
      -- was `simpa using [...]` and very slow
      -- (https://github.com/leanprover-community/mathlib4/issues/19751)
      simpa only [zsmul_eq_mul, Int.cast_add, Pi.intCast_def, Int.cast_one] using
        (rootSpaceWeightSpaceProduct R L H M α (k • α + χ) ((k + 1) • α + χ)
            (by rw [add_smul]; abel) (⟨x, hx⟩ ⊗ₜ ⟨z, hz⟩)).property
    rw [LieModule.genWeightSpaceChain]
    rcases eq_or_ne (k + 1) q with rfl | hk'; · simp only [hq, bot_le]
    replace hk' : k + 1 ∈ Ioo p q := ⟨by linarith [hk.1], lt_of_le_of_ne hk.2 hk'⟩
    exact le_biSup (fun k ↦ genWeightSpace M (k • α + χ)) hk'
  | zero => simp
  | add _ _ _ _ hz₁ hz₂ => rw [lie_add]; exact add_mem hz₁ hz₂

