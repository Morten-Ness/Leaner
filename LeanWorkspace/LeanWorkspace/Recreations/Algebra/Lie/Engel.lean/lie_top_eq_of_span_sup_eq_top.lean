import Mathlib

variable {R : Type u₁} {L : Type u₂} {L₂ : Type u₃} {M : Type u₄}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable {I : LieIdeal R L} {x : L} (hxI : R ∙ x ⊔ I = ⊤)

theorem lie_top_eq_of_span_sup_eq_top (N : LieSubmodule R L M) :
    (↑⁅(⊤ : LieIdeal R L), N⁆ : Submodule R M) =
      (N : Submodule R M).map (toEnd R L M x) ⊔ (↑⁅I, N⁆ : Submodule R M) := by
  simp only [lieIdeal_oper_eq_linear_span', Submodule.sup_span, mem_top, true_and,
    Submodule.map_coe, toEnd_apply_apply]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono fun z hz => ?_)
  · rintro z ⟨y, n, hn : n ∈ N, rfl⟩
    obtain ⟨t, z, hz, rfl⟩ := LieSubmodule.exists_smul_add_of_span_sup_eq_top hxI y
    simp only [SetLike.mem_coe, Submodule.span_union, Submodule.mem_sup]
    exact
      ⟨t • ⁅x, n⁆, Submodule.subset_span ⟨t • n, N.smul_mem' t hn, lie_smul t x n⟩, ⁅z, n⁆,
        Submodule.subset_span ⟨z, hz, n, hn, rfl⟩, by simp⟩
  · rcases hz with (⟨m, hm, rfl⟩ | ⟨y, -, m, hm, rfl⟩)
    exacts [⟨x, m, hm, rfl⟩, ⟨y, m, hm, rfl⟩]

