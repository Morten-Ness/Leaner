import Mathlib

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {N : ι → Submodule R M}

variable [DecidableEq ι]

theorem diag_toMatrix_directSum_collectedBasis_eq_zero_of_mapsTo_ne
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]
    {s : Finset ι} (h : IsInternal fun i : s ↦ N i)
    (b : (i : s) → Module.Basis (κ i) R (N i)) (σ : ι → ι) (hσ : ∀ i, σ i ≠ i)
    {f : Module.End R M} (hf : ∀ i, MapsTo f (N i) (N <| σ i)) (hN : ∀ i, i ∉ s → N i = ⊥) :
    Matrix.diag (toMatrix (h.collectedBasis b) (h.collectedBasis b) f) = 0 := by
  ext ⟨i, k⟩
  simp only [Matrix.diag_apply, Pi.zero_apply, toMatrix_apply, IsInternal.collectedBasis_coe]
  by_cases hi : σ i ∈ s
  · let j : s := ⟨σ i, hi⟩
    replace hσ : j ≠ i := fun hij ↦ hσ i <| Subtype.ext_iff.mp hij
    exact h.collectedBasis_repr_of_mem_ne b hσ <| hf _ <| Subtype.mem (b i k)
  · suffices f (b i k) = 0 by simp [this]
    simpa [hN _ hi] using hf i <| Subtype.mem (b i k)

