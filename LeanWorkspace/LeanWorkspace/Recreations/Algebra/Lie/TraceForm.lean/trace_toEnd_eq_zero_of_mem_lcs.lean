import Mathlib

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

theorem trace_toEnd_eq_zero_of_mem_lcs
    {k : ℕ} {x : L} (hk : 1 ≤ k) (hx : x ∈ lowerCentralSeries R L L k) :
    trace R _ (toEnd R L M x) = 0 := by
  replace hx : x ∈ lowerCentralSeries R L L 1 := antitone_lowerCentralSeries _ _ _ hk hx
  replace hx : x ∈ Submodule.span R {m | ∃ u v : L, ⁅u, v⁆ = m} := by
    rw [lowerCentralSeries_succ, ← LieSubmodule.mem_toSubmodule,
      LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
    simpa using hx
  refine Submodule.span_induction (p := fun x _ ↦ trace R _ (toEnd R L M x) = 0)
    ?_ ?_ (fun u v _ _ hu hv ↦ ?_) (fun t u _ hu ↦ ?_) hx
  · intro y ⟨u, v, huv⟩
    simp [← huv]
  · simp
  · simp [hu, hv]
  · simp [hu]

