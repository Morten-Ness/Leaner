import Mathlib

variable {R M K P : Type*} [Ring R] [AddCommGroup M] [AddCommGroup K] [AddCommGroup P]

variable [Module R M] [Module R K] [Module R P]

variable {f : K →ₗ[R] M} {g : M →ₗ[R] P} {s : M →ₗ[R] K}

variable (hs : s ∘ₗ f = LinearMap.id) (hfg : Function.Exact f g)

variable {ι κ σ : Type*} {v : ι → M} {a : κ → ι} {b : σ → ι}

private theorem top_le_span_of_aux (v : κ ⊕ σ → M)
    (hg : Function.Surjective g) (hslzero : ∀ i, s (v (.inl i)) = 0)
    (hli : LinearIndependent R (s ∘ v ∘ .inr)) (hsp : ⊤ ≤ Submodule.span R (Set.range v)) :
    ⊤ ≤ Submodule.span R (Set.range <| g ∘ v ∘ .inl) := by
  rintro p -
  obtain ⟨m, rfl⟩ := hg p
  wlog h : m ∈ LinearMap.ker s
  · let x : M := f (s m)
    rw [show g m = g (m - f (s m)) by simp [hfg.apply_apply_eq_zero]]
    apply this hs hfg v hg hslzero hli hsp
    replace hs := DFunLike.congr_fun hs (s m)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hs
    simp [hs]
  have : m ∈ Submodule.span R (Set.range v) := hsp Submodule.mem_top
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp this
  simp only [LinearMap.mem_ker, Finsupp.sum, map_sum, map_smul,
    Finset.sum_sum_eq_sum_toLeft_add_sum_toRight, map_add, hslzero, smul_zero,
    Finset.sum_const_zero, zero_add] at h
  replace hli := (linearIndependent_iff'.mp hli) c.support.toRight (c ∘ .inr) h
  simp only [Finset.mem_toRight, Finsupp.mem_support_iff, Function.comp_apply, not_imp_self] at hli
  simp only [Finsupp.sum, Finset.sum_sum_eq_sum_toLeft_add_sum_toRight, hli, zero_smul,
    Finset.sum_const_zero, add_zero, map_sum, map_smul]
  exact Submodule.sum_mem _ (fun i hi ↦ Submodule.smul_mem _ _ <| Submodule.subset_span ⟨i, rfl⟩)


theorem LinearMap.linearProjOfIsCompl_comp_bijective_of_exact
    (hf : Function.Injective f) {q : Submodule R M} {E : Type*} [AddCommGroup E] [Module R E]
    {i : E →ₗ[R] M} (hi : Function.Injective i) (h : IsCompl (LinearMap.range i) q)
    (hker : Disjoint (LinearMap.ker g) q) (hmap : Submodule.map g q = ⊤) :
    Function.Bijective (LinearMap.linearProjOfIsCompl q i hi h ∘ₗ f) := by
  rw [LinearMap.linearProjOfIsCompl, LinearMap.comp_assoc, LinearMap.coe_comp,
      Function.Bijective.of_comp_iff]
  · exact (LinearEquiv.ofInjective i hi).symm.bijective
  · exact Submodule.linearProjOfIsCompl_comp_bijective_of_exact hfg hf h hker hmap

