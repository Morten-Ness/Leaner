import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem traceForm_eq_zero_if_mem_lcs_of_mem_ucs {x y : L} (k : ℕ)
    (hx : x ∈ (⊤ : LieIdeal R L).lcs L k) (hy : y ∈ (⊥ : LieIdeal R L).ucs k) :
    LieModule.traceForm R L M x y = 0 := by
  induction k generalizing x y with
  | zero =>
    replace hy : y = 0 := by simpa using hy
    simp [hy]
  | succ k ih =>
    rw [LieSubmodule.ucs_succ, LieSubmodule.mem_normalizer] at hy
    simp_rw [LieIdeal.lcs_succ, ← LieSubmodule.mem_toSubmodule,
      LieSubmodule.lieIdeal_oper_eq_linear_span', LieSubmodule.mem_top, true_and] at hx
    refine Submodule.span_induction ?_ ?_ (fun z w _ _ hz hw ↦ ?_) (fun t z _ hz ↦ ?_) hx
    · rintro - ⟨z, w, hw, rfl⟩
      rw [← lie_skew, map_neg, LinearMap.neg_apply, neg_eq_zero, LieModule.traceForm_apply_lie_apply]
      exact ih hw (hy _)
    · simp
    · simp [hz, hw]
    · simp [hz]

