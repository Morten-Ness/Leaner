import Mathlib

variable {R : Type u₁} {L : Type u₂} {L₂ : Type u₃} {M : Type u₄}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem LieAlgebra.isEngelian_of_isNoetherian [IsNoetherian R L] : LieAlgebra.IsEngelian R L := by
  intro M _i1 _i2 _i3 _i4 h
  rw [← isNilpotent_range_toEnd_iff R]
  let L' := (toEnd R L M).range
  replace h : ∀ y : L', IsNilpotent (y : Module.End R M) := by
    rintro ⟨-, ⟨y, rfl⟩⟩
    simp [h]
  change LieModule.IsNilpotent L' M
  let s := {K : LieSubalgebra R L' | LieAlgebra.IsEngelian R K}
  have hs : s.Nonempty := ⟨⊥, LieAlgebra.isEngelian_of_subsingleton⟩
  suffices ⊤ ∈ s by
    rw [← isNilpotent_of_top_iff (R := R)]
    apply this M
    simp [LieSubalgebra.toEnd_eq, h]
  have : ∀ K ∈ s, K ≠ ⊤ → ∃ K' ∈ s, K < K' := by
    rintro K (hK₁ : LieAlgebra.IsEngelian R K) hK₂
    apply LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer hK₁
    apply lt_of_le_of_ne K.le_normalizer
    rw [Ne, eq_comm, K.normalizer_eq_self_iff, ← Ne, ←
      LieSubmodule.nontrivial_iff_ne_bot R K]
    have : Nontrivial (L' ⧸ K.toLieSubmodule) := Submodule.Quotient.nontrivial_iff.2 <| by simpa
    have : LieModule.IsNilpotent K (L' ⧸ K.toLieSubmodule) := by
      refine hK₁ _ fun x => ?_
      have hx := LieAlgebra.isNilpotent_ad_of_isNilpotent (h x)
      apply Module.End.IsNilpotent.mapQ ?_ hx
      intro X HX
      simp only [LieSubalgebra.coe_toLieSubmodule, LieSubalgebra.mem_toSubmodule] at HX
      simp only [LieSubalgebra.coe_toLieSubmodule, Submodule.mem_comap, ad_apply,
        LieSubalgebra.mem_toSubmodule]
      exact LieSubalgebra.lie_mem K x.prop HX
    exact nontrivial_max_triv_of_isNilpotent R K (L' ⧸ K.toLieSubmodule)
  haveI _i5 : IsNoetherian R L' := by
    refine isNoetherian_of_surjective (LieHom.rangeRestrict (toEnd R L M)).toLinearMap ?_
    simp only [LinearMap.range_eq_top]
    exact LieHom.surjective_rangeRestrict (toEnd R L M)
  obtain ⟨K, hK₁, hK₂⟩ := (LieSubalgebra.wellFoundedGT_of_noetherian R L').wf.has_min s hs
  obtain rfl : K = ⊤ := by grind
  exact hK₁

