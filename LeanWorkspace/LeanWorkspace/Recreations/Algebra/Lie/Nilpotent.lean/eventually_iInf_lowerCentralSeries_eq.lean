import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (k : ℕ) (N : LieSubmodule R L M)

variable {M₂ : Type w₁} [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂]

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


theorem eventually_iInf_lowerCentralSeries_eq [IsArtinian R M] :
    ∀ᶠ l in Filter.atTop, ⨅ k, LieModule.lowerCentralSeries R L M k = LieModule.lowerCentralSeries R L M l := by
  have h_wf : WellFoundedGT (LieSubmodule R L M)ᵒᵈ :=
    LieSubmodule.wellFoundedLT_of_isArtinian R L M
  obtain ⟨n, hn : ∀ m, n ≤ m → LieModule.lowerCentralSeries R L M n = LieModule.lowerCentralSeries R L M m⟩ :=
    h_wf.monotone_chain_condition ⟨_, LieModule.antitone_lowerCentralSeries R L M⟩
  refine Filter.eventually_atTop.mpr ⟨n, fun l hl ↦ le_antisymm (iInf_le _ _) (le_iInf fun m ↦ ?_)⟩
  rcases le_or_gt l m with h | h
  · rw [← hn _ hl, ← hn _ (hl.trans h)]
  · exact LieModule.antitone_lowerCentralSeries R L M (le_of_lt h)

