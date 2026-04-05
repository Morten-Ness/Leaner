import Mathlib

variable (R : Type u) (L : Type v) (L' : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

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


theorem LieAlgebra.nilpotent_of_nilpotent_quotient {I : LieIdeal R L} (h₁ : I ≤ center R L)
    (h₂ : IsNilpotent (L ⧸ I)) : IsNilpotent L := by
  suffices LieModule.IsNilpotent L (L ⧸ I) by
    exact LieModule.nilpotentOfNilpotentQuotient R L L h₁ this
  simp only [LieRing.IsNilpotent, LieModule.isNilpotent_iff R] at h₂ ⊢
  peel h₂ with k hk
  simp [← LieSubmodule.toSubmodule_inj, coe_lowerCentralSeries_ideal_quot_eq, hk]

