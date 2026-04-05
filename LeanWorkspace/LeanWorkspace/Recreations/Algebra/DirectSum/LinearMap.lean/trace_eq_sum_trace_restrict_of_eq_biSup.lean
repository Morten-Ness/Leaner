import Mathlib

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {N : ι → Submodule R M}

theorem trace_eq_sum_trace_restrict_of_eq_biSup
    [∀ i, Module.Finite R (N i)] [∀ i, Module.Free R (N i)]
    (s : Finset ι) (h : iSupIndep <| fun i : s ↦ N i)
    {f : Module.End R M} (hf : ∀ i, MapsTo f (N i) (N i))
    (p : Submodule R M) (hp : p = ⨆ i ∈ s, N i)
    (hp' : MapsTo f p p := hp ▸ LinearMap.mapsTo_biSup_of_mapsTo (s : Set ι) hf) :
    trace R p (f.restrict hp') = ∑ i ∈ s, trace R (N i) (f.restrict (hf i)) := by
  classical
  let N' : s → Submodule R p := fun i ↦ (N i).comap p.subtype
  replace h : IsInternal N' := hp ▸ isInternal_biSup_submodule_of_iSupIndep (s : Set ι) h
  have hf' : ∀ i, MapsTo (restrict f hp') (N' i) (N' i) := fun i x hx' ↦ by simpa using hf i hx'
  let e : (i : s) → N' i ≃ₗ[R] N i := fun ⟨i, hi⟩ ↦ (N i).comapSubtypeEquivOfLe (hp ▸ le_biSup N hi)
  have _i1 : ∀ i, Module.Finite R (N' i) := fun i ↦ Module.Finite.equiv (e i).symm
  have _i2 : ∀ i, Module.Free R (N' i) := fun i ↦ Module.Free.of_equiv (e i).symm
  rw [LinearMap.trace_eq_sum_trace_restrict h hf', ← s.sum_coe_sort]
  have : ∀ i : s, f.restrict (hf i) = (e i).conj ((f.restrict hp').restrict (hf' i)) := fun _ ↦ rfl
  simp [this]

