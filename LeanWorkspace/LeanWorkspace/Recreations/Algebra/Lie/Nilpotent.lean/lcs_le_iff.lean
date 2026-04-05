import Mathlib

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M]

variable (k : ℕ) (N : LieSubmodule R L M)

variable {N₁ N₂ : LieSubmodule R L M}

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


theorem lcs_le_iff (k : ℕ) : N₁.lcs k ≤ N₂ ↔ N₁ ≤ N₂.ucs k := by
  convert LieSubmodule.lcs_add_le_iff (R := R) (L := L) (M := M) 0 k
  rw [zero_add]

