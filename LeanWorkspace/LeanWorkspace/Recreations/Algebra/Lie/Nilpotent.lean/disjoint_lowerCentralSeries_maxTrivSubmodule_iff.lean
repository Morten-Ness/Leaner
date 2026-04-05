import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (k : ℕ) (N : LieSubmodule R L M)

variable {M₂ : Type w₁} [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂]

variable [LieModule R L M]

private theorem coe_lowerCentralSeries_eq_int_aux (R₁ R₂ L M : Type*)
    [CommRing R₁] [CommRing R₂] [AddCommGroup M]
    [LieRing L] [LieAlgebra R₁ L] [LieAlgebra R₂ L] [Module R₁ M] [Module R₂ M] [LieRingModule L M]
    [LieModule R₁ L M] (k : ℕ) :
    let I := LieModule.lowerCentralSeries R₂ L M k; let S : Set M := {⁅a, b⁆ | (a : L) (b ∈ I)}
    (Submodule.span R₁ S : Set M) ≤ (Submodule.span R₂ S : Set M) := by
  intro I S x hx
  simp only [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.closure_induction with
  | zero => exact Submodule.zero_mem _
  | add y z hy₁ hz₁ hy₂ hz₂ => exact Submodule.add_mem _ hy₂ hz₂
  | smul_mem c y hy =>
      obtain ⟨a, b, hb, rfl⟩ := hy
      rw [← smul_lie]
      exact Submodule.subset_span ⟨c • a, b, hb, rfl⟩


theorem disjoint_lowerCentralSeries_maxTrivSubmodule_iff [IsNilpotent L M] :
    Disjoint (LieModule.lowerCentralSeries R L M 1) (maxTrivSubmodule R L M) ↔ IsTrivial L M := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp⟩
  nontriviality M
  by_contra contra
  have : LieModule.lowerCentralSeriesLast R L M ≤ LieModule.lowerCentralSeries R L M 1 ⊓ maxTrivSubmodule R L M :=
    le_inf_iff.mpr ⟨LieModule.lowerCentralSeriesLast_le_of_not_isTrivial R L M contra,
      LieModule.lowerCentralSeriesLast_le_max_triv R L M⟩
  suffices ¬ Nontrivial (LieModule.lowerCentralSeriesLast R L M) by
    exact this (LieModule.nontrivial_lowerCentralSeriesLast R L M)
  rw [h.eq_bot, le_bot_iff] at this
  exact this ▸ not_nontrivial _

