import Mathlib

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (I : LieIdeal R L)

variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M]

variable (k : ℕ)

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


set_option backward.isDefEq.respectTransparency false in
theorem coe_lcs_eq [LieModule R L M] :
    LieSubmodule.toSubmodule (I.lcs M k) = LieModule.lowerCentralSeries R I M k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp_rw [LieModule.lowerCentralSeries_succ, LieIdeal.lcs_succ, LieSubmodule.lieIdeal_oper_eq_linear_span', ←
      (I.lcs M k).mem_toSubmodule, ih, LieSubmodule.mem_toSubmodule, LieSubmodule.mem_top,
      true_and, (I : LieSubalgebra R L).coe_bracket_of_module]
    simp

