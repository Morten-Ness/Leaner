import Mathlib

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {N : ι → Submodule R M}

variable [DecidableEq ι]

variable [∀ i, Module.Finite R (N i)] [∀ i, Module.Free R (N i)]

theorem trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero
    [IsDomain R] [IsPrincipalIdealRing R] [Module.Free R M] [Module.Finite R M]
    {f g : Module.End R M}
    (h_comm : Commute f g)
    (hf : ⨆ μ, f.maxGenEigenspace μ = ⊤)
    (hg : ∀ μ, trace R _ (g.restrict (f.mapsTo_maxGenEigenspace_of_comm h_comm μ)) = 0) :
    trace R _ (g ∘ₗ f) = 0 := by
  have hfg : ∀ μ,
      MapsTo (g ∘ₗ f) ↑(f.maxGenEigenspace μ) ↑(f.maxGenEigenspace μ) :=
    fun μ ↦ (f.mapsTo_maxGenEigenspace_of_comm h_comm μ).comp
      (f.mapsTo_maxGenEigenspace_of_comm rfl μ)
  suffices ∀ μ, trace R _ ((g ∘ₗ f).restrict (hfg μ)) = 0 by
    classical
    have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      f.independent_maxGenEigenspace hf
    have h_fin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
      WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
    simp [LinearMap.trace_eq_sum_trace_restrict' hds h_fin hfg, this]
  intro μ
  have hf' := f.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) μ
  have hg' := f.mapsTo_maxGenEigenspace_of_comm h_comm μ
  replace h_comm : Commute (g.restrict (f.mapsTo_maxGenEigenspace_of_comm h_comm μ))
      (f.restrict (f.mapsTo_maxGenEigenspace_of_comm rfl μ)) :=
    restrict_commute h_comm.symm _ _
  have := f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
  rw [restrict_comp hf' hg', trace_comp_eq_mul_of_commute_of_isNilpotent μ h_comm this,
    hg, mul_zero]

