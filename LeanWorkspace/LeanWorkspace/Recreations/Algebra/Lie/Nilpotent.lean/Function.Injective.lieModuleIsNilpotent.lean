import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (k : ℕ) (N : LieSubmodule R L M)

variable [LieModule R L M]

variable {L₂ M₂ : Type*} [LieRing L₂] [LieAlgebra R L₂]

variable [AddCommGroup M₂] [Module R M₂] [LieRingModule L₂ M₂]

variable {f : L →ₗ⁅R⁆ L₂} {g : M →ₗ[R] M₂}

variable (hfg : ∀ x m, ⁅f x, g m⁆ = g ⁅x, m⁆)

variable [LieModule R L₂ M₂] (hg_inj : Function.Injective g)

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


include hg_inj hfg in
theorem Function.Injective.lieModuleIsNilpotent [IsNilpotent L₂ M₂] : IsNilpotent L M := by
  obtain ⟨k, hk⟩ := LieModule.IsNilpotent.nilpotent R L₂ M₂
  rw [LieModule.isNilpotent_iff R]
  use k
  rw [← LieSubmodule.toSubmodule_inj] at hk ⊢
  apply Submodule.map_injective_of_injective hg_inj
  simpa [hk] using lieModule_lcs_map_le hfg k

