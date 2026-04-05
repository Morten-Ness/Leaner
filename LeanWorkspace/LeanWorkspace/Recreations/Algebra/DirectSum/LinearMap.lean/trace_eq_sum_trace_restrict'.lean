import Mathlib

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {N : ι → Submodule R M}

variable [DecidableEq ι]

variable [∀ i, Module.Finite R (N i)] [∀ i, Module.Free R (N i)]

theorem trace_eq_sum_trace_restrict' (h : IsInternal N) (hN : {i | N i ≠ ⊥}.Finite)
    {f : M →ₗ[R] M} (hf : ∀ i, MapsTo f (N i) (N i)) :
    trace R M f = ∑ i ∈ hN.toFinset, trace R (N i) (f.restrict (hf i)) := by
  let _ : Fintype {i // N i ≠ ⊥} := hN.fintype
  let _ : Fintype {i | N i ≠ ⊥} := hN.fintype
  rw [← Finset.sum_coe_sort, LinearMap.trace_eq_sum_trace_restrict (isInternal_ne_bot_iff.mpr h) (hf ·)]
  exact Fintype.sum_equiv hN.subtypeEquivToFinset _ _ (fun i ↦ rfl)

