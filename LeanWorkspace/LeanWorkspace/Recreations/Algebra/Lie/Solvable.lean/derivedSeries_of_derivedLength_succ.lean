import Mathlib

variable (R : Type u) (L : Type v) (M : Type w) {L' : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (I J : LieIdeal R L) {f : L' →ₗ⁅R⁆ L}

private theorem coe_derivedSeries_eq_int_aux (R₁ R₂ L : Type*) [CommRing R₁] [CommRing R₂]
    [LieRing L] [LieAlgebra R₁ L] [LieAlgebra R₂ L] (k : ℕ)
    (ih : ∀ (x : L), x ∈ LieAlgebra.derivedSeriesOfIdeal R₁ L k ⊤ ↔ x ∈ LieAlgebra.derivedSeriesOfIdeal R₂ L k ⊤) :
    let I := LieAlgebra.derivedSeriesOfIdeal R₂ L k ⊤; let S : Set L := {⁅a, b⁆ | (a ∈ I) (b ∈ I)}
    (Submodule.span R₁ S : Set L) ≤ (Submodule.span R₂ S : Set L) := by
  intro I S x hx
  simp only [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.closure_induction with
  | zero => exact Submodule.zero_mem _
  | add y z hy₁ hz₁ hy₂ hz₂ => exact Submodule.add_mem _ hy₂ hz₂
  | smul_mem c y hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      rw [← smul_lie]
      refine Submodule.subset_span ⟨c • a, ?_, b, hb, rfl⟩
      rw [← ih] at ha ⊢
      exact Submodule.smul_mem _ _ ha


theorem derivedSeries_of_derivedLength_succ (I : LieIdeal R L) (k : ℕ) :
    LieAlgebra.derivedLengthOfIdeal R L I = k + 1 ↔
      IsLieAbelian (LieAlgebra.derivedSeriesOfIdeal R L k I) ∧ LieAlgebra.derivedSeriesOfIdeal R L k I ≠ ⊥ := by
  rw [LieAlgebra.abelian_iff_derived_succ_eq_bot]
  let s := { k | LieAlgebra.derivedSeriesOfIdeal R L k I = ⊥ }
  change sInf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s
  have hs : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s := by
    intro k₁ k₂ h₁₂ h₁
    suffices LieAlgebra.derivedSeriesOfIdeal R L k₂ I ≤ ⊥ by exact eq_bot_iff.mpr this
    change LieAlgebra.derivedSeriesOfIdeal R L k₁ I = ⊥ at h₁; rw [← h₁]
    exact LieAlgebra.derivedSeriesOfIdeal_antitone I h₁₂
  exact Nat.sInf_upward_closed_eq_succ_iff hs k

