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


theorem nilpotencyLength_eq_succ_iff (k : ℕ) :
    LieModule.nilpotencyLength L M = k + 1 ↔
      LieModule.lowerCentralSeries R L M (k + 1) = ⊥ ∧ LieModule.lowerCentralSeries R L M k ≠ ⊥ := by
  have aux (k : ℕ) : LieModule.lowerCentralSeries R L M k = ⊥ ↔ LieModule.lowerCentralSeries ℤ L M k = ⊥ := by
    simp [SetLike.ext'_iff, LieModule.coe_lowerCentralSeries_eq_int R L M]
  let s := {k | LieModule.lowerCentralSeries ℤ L M k = ⊥}
  rw [aux, ne_eq, aux]
  change sInf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s
  have hs : ∀ k₁ k₂, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s := by
    rintro k₁ k₂ h₁₂ (h₁ : LieModule.lowerCentralSeries ℤ L M k₁ = ⊥)
    exact eq_bot_iff.mpr (h₁ ▸ LieModule.antitone_lowerCentralSeries ℤ L M h₁₂)
  exact Nat.sInf_upward_closed_eq_succ_iff hs k

