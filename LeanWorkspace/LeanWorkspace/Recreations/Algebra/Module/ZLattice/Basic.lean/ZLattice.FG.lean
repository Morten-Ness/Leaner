import Mathlib

variable (K : Type*) [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [HasSolidNorm K] [FloorRing K]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]

variable [ProperSpace E] (L : Submodule ℤ E) [DiscreteTopology L]

theorem ZLattice.FG [hs : IsZLattice K L] : L.FG := by
  obtain ⟨s, ⟨h_incl, ⟨h_span, h_lind⟩⟩⟩ := exists_linearIndependent K (L : Set E)
  -- Let `s` be a maximal `K`-linear independent family of elements of `L`. We show that
  -- `L` is finitely generated (as a ℤ-module) because it fits in the exact sequence
  -- `0 → span ℤ s → L → L ⧸ span ℤ s → 0` with `span ℤ s` and `L ⧸ span ℤ s` finitely generated.
  refine fg_of_fg_map_of_fg_inf_ker (span ℤ s).mkQ ?_ ?_
  · -- Let `b` be the `K`-basis of `E` formed by the vectors in `s`. The elements of
    -- `L ⧸ span ℤ s = L ⧸ span ℤ b` are in bijection with elements of `L ∩ ZSpan.fundamentalDomain b`
    -- so there are finitely many since `ZSpan.fundamentalDomain b` is bounded.
    refine fg_def.mpr ⟨ZSpan.map (span ℤ s).mkQ L, ?_, span_eq _⟩
    let b := Module.Basis.mk h_lind (by
      rw [← ZSpan.span_top hs, ← h_span]
      exact span_mono (by simp only [Subtype.range_coe_subtype, Set.setOf_mem_eq, subset_rfl]))
    rw [show span ℤ s = span ℤ (Set.range b) by simp [b, Module.Basis.coe_mk, Subtype.range_coe_subtype]]
    have : Fintype s := h_lind.setFinite.fintype
    refine Set.Finite.of_finite_image (f := ((↑) : _ → E) ∘ ZSpan.quotientEquiv b) ?_
      (Function.Injective.injOn (Subtype.coe_injective.comp (ZSpan.quotientEquiv b).injective))
    have : ((ZSpan.fundamentalDomain b) ∩ L).Finite := by
      change ((ZSpan.fundamentalDomain b) ∩ L.toAddSubgroup).Finite
      have : DiscreteTopology L.toAddSubgroup := (inferInstance : DiscreteTopology L)
      exact Metric.finite_isBounded_inter_isClosed
        DiscreteTopology.isDiscrete (ZSpan.fundamentalDomain_isBounded b) inferInstance
    refine Set.Finite.subset this ?_
    rintro _ ⟨_, ⟨⟨x, ⟨h_mem, rfl⟩⟩, rfl⟩⟩
    rw [Function.comp_apply, mkQ_apply, ZSpan.quotientEquiv_apply_mk, ZSpan.fractRestrict_apply]
    refine ⟨?_, ?_⟩
    · exact ZSpan.fract_mem_fundamentalDomain b x
    · rw [ZSpan.fract, SetLike.mem_coe, sub_eq_add_neg]
      refine Submodule.add_mem _ h_mem
        (neg_mem (Set.mem_of_subset_of_mem ?_ (Subtype.mem (ZSpan.floor b x))))
      rw [SetLike.coe_subset_coe, Module.Basis.coe_mk, Subtype.range_coe_subtype, Set.setOf_mem_eq]
      exact span_le.mpr h_incl
  · -- `span ℤ s` is finitely generated because `s` is finite
    rw [ker_mkQ, inf_of_le_right (span_le.mpr h_incl)]
    exact fg_span (LinearIndependent.setFinite h_lind)

