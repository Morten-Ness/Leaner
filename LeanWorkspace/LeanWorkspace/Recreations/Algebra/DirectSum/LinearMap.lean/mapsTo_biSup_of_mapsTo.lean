import Mathlib

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {N : ι → Submodule R M}

variable [DecidableEq ι]

variable [∀ i, Module.Finite R (N i)] [∀ i, Module.Free R (N i)]

theorem mapsTo_biSup_of_mapsTo {ι : Type*} {N : ι → Submodule R M}
    (s : Set ι) {f : Module.End R M} (hf : ∀ i, MapsTo f (N i) (N i)) :
    MapsTo f ↑(⨆ i ∈ s, N i) ↑(⨆ i ∈ s, N i) := by
  replace hf : ∀ i, (N i).map f ≤ N i := fun i ↦ Submodule.map_le_iff_le_comap.mpr (hf i)
  suffices (⨆ i ∈ s, N i).map f ≤ ⨆ i ∈ s, N i from Submodule.map_le_iff_le_comap.mp this
  simpa only [Submodule.map_iSup] using iSup₂_mono <| fun i _ ↦ hf i

