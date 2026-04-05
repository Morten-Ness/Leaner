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


include hfg in
theorem lieModule_lcs_map_le (k : ℕ) :
    (LieModule.lowerCentralSeries R L M k : Submodule R M).map g ≤ LieModule.lowerCentralSeries R L₂ M₂ k := by
  induction k with
  | zero =>
    simp [Submodule.map_top]
  | succ k ih =>
    rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span', Submodule.map_span,
      Submodule.span_le]
    rintro m₂ ⟨m, ⟨x, n, m_n, ⟨h₁, h₂⟩⟩, rfl⟩
    simp only [LieModule.lowerCentralSeries_succ, SetLike.mem_coe, LieSubmodule.mem_toSubmodule]
    have : ∃ y : L₂, ∃ n : LieModule.lowerCentralSeries R L₂ M₂ k, ⁅y, n⁆ = g m := by
      use f x, ⟨g m_n, ih (Submodule.mem_map_of_mem h₁)⟩
      simp [hfg x m_n, h₂]
    obtain ⟨y, n, hn⟩ := this
    rw [← hn]
    apply LieSubmodule.lie_mem_lie
    · simp
    · exact SetLike.coe_mem n

