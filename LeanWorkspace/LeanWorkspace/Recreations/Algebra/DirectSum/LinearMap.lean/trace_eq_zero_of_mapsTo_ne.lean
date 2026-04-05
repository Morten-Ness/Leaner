import Mathlib

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {N : ι → Submodule R M}

variable [DecidableEq ι]

variable [∀ i, Module.Finite R (N i)] [∀ i, Module.Free R (N i)]

theorem trace_eq_zero_of_mapsTo_ne (h : IsInternal N) [IsNoetherian R M]
    (σ : ι → ι) (hσ : ∀ i, σ i ≠ i) {f : Module.End R M}
    (hf : ∀ i, MapsTo f (N i) (N <| σ i)) :
    trace R M f = 0 := by
  have hN : {i | N i ≠ ⊥}.Finite := WellFoundedGT.finite_ne_bot_of_iSupIndep
    h.submodule_iSupIndep
  let s := hN.toFinset
  let κ := fun i ↦ Module.Free.ChooseBasisIndex R (N i)
  let b : (i : s) → Module.Basis (κ i) R (N i) := fun i ↦ Module.Free.chooseBasis R (N i)
  replace h : IsInternal fun i : s ↦ N i := by
    convert DirectSum.isInternal_ne_bot_iff.mpr h <;> simp [s]
  simp_rw [trace_eq_matrix_trace R (h.collectedBasis b), Matrix.trace,
    LinearMap.diag_toMatrix_directSum_collectedBasis_eq_zero_of_mapsTo_ne h b σ hσ hf (by simp [s]),
    Pi.zero_apply, Finset.sum_const_zero]

