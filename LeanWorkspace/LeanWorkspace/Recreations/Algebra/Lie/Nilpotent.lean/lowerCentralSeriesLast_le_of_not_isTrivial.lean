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


theorem lowerCentralSeriesLast_le_of_not_isTrivial [IsNilpotent L M] (h : ¬ IsTrivial L M) :
    LieModule.lowerCentralSeriesLast R L M ≤ LieModule.lowerCentralSeries R L M 1 := by
  rw [LieModule.lowerCentralSeriesLast]
  replace h : 1 < LieModule.nilpotencyLength L M := by
    by_contra contra
    have := LieModule.isTrivial_of_nilpotencyLength_le_one L M (not_lt.mp contra)
    contradiction
  rcases hk : LieModule.nilpotencyLength L M with - | k <;> rw [hk] at h
  · contradiction
  · exact LieModule.antitone_lowerCentralSeries _ _ _ (Nat.le_of_lt_succ h)

