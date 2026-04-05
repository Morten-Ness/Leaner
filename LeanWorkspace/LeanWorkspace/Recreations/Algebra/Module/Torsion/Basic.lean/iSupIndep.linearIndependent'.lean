import Mathlib

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

theorem iSupIndep.linearIndependent' {ι R M : Type*} {v : ι → M} [Ring R]
    [AddCommGroup M] [Module R M] (hv : iSupIndep fun i => R ∙ v i)
    (h_ne_zero : ∀ i, Ideal.torsionOf R M (v i) = ⊥) : LinearIndependent R v := by
  refine linearIndependent_iff_eq_zero_of_smul_mem_span.mpr fun i r hi => ?_
  replace hv := iSupIndep_def.mp hv i
  simp only [iSup_subtype', ← Submodule.span_range_eq_iSup (ι := Subtype _), disjoint_iff] at hv
  have : r • v i ∈ (⊥ : Submodule R M) := by
    rw [← hv, Submodule.mem_inf]
    refine ⟨Submodule.mem_span_singleton.mpr ⟨r, rfl⟩, ?_⟩
    convert hi
    ext
    simp
  rw [← Submodule.mem_bot R, ← h_ne_zero i]
  simpa using this

