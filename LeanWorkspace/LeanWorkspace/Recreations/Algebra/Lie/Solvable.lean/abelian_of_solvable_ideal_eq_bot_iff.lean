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


theorem abelian_of_solvable_ideal_eq_bot_iff (I : LieIdeal R L) [h : IsSolvable I] :
    LieAlgebra.derivedAbelianOfIdeal I = ⊥ ↔ I = ⊥ := by
  dsimp only [LieAlgebra.derivedAbelianOfIdeal]
  split
  · simp_all only [LieAlgebra.derivedLength_zero]
  · rename_i k h
    obtain ⟨_, h₂⟩ := (LieAlgebra.derivedSeries_of_derivedLength_succ R L I k).mp h
    have h₃ : I ≠ ⊥ := by rintro rfl; apply h₂; apply LieAlgebra.derivedSeries_of_bot_eq_bot
    simp only [h₂, h₃]

